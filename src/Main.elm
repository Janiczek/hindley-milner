module Main exposing (main)

import Dict exposing (Dict)
import Set exposing (Set)


main =
    Platform.worker
        { init = \() -> ( Debug.log "RESULT" computation, Cmd.none )
        , update = \_ m -> ( m, Cmd.none )
        , subscriptions = \_ -> Sub.none
        }


computation =
    let
        typed =
            exampleExpr
                |> Debug.log "EXPR"
                |> assignIds

        substMap =
            typed
                |> Result.andThen (generateEquations >> unifyAllEquations)
    in
    Result.map2
        (\( _, type_ ) subst ->
            getType type_ subst
        )
        typed
        substMap


type Expr
    = Int Int
    | Var String -- name
    | Plus Expr Expr -- left, right
    | Lambda String Expr -- argument, body


{-| This should be:

    myFn : Int -> Int -> Int
    myFn a b =
        a + b + 1
    myFn =
        \a ->
            \b ->
                a + b + 1

-}
exampleExpr : Expr
exampleExpr =
    Lambda "a" <|
        Lambda "b" <|
            Plus
                (Plus
                    (Var "a")
                    (Var "b")
                )
                (Int 1)



-- TYPING
-- Hindley-Milner
-- https://eli.thegreenplace.net/2018/type-inference/
-- https://github.com/eliben/code-for-blog/blob/master/2018/type-inference/typing.py


{-| We use this trick (note that TypedExpr\_ recurs on TypedExpr, not on itself)
to hold additional state (the Type).
-}
type alias TypedExpr =
    ( TypedExpr_, Type )


type TypedExpr_
    = TyInt Int
    | TyVar String -- name
    | TyPlus TypedExpr TypedExpr -- left, right
    | TyLambda String TypedExpr Int -- argument, body, argument id (to be used in TVar)


type Type
    = TVar Int
    | TInt
    | TFunction Type Type


type TypeError
    = UnboundName String
    | CannotUnify Type Type
    | VarOccursInType Int Type


getVarId : Type -> Maybe Int
getVarId type_ =
    case type_ of
        TVar id ->
            Just id

        _ ->
            Nothing



-- STAGE 1: Assign IDs (in `TVar`s) to all subexpressions (well, except integers)


assignIds : Expr -> Result TypeError TypedExpr
assignIds expr =
    assignIdsHelp 0 Dict.empty expr
        -- why's there no Tuple.third?
        |> Result.map (\( _, _, typedExpr ) -> typedExpr)


assignIdsHelp : Int -> Dict String Int -> Expr -> Result TypeError ( Int, Dict String Int, TypedExpr )
assignIdsHelp unusedId0 varIds0 expr =
    (case expr of
        Int int ->
            Ok
                ( unusedId0
                , varIds0
                , TyInt int
                )

        Var name ->
            Ok
                ( unusedId0
                , Dict.insert name unusedId0 varIds0
                , TyVar name
                )

        Plus e1 e2 ->
            -- elm-format makes this look ugly ... is there a different way?
            assignIdsHelp unusedId0 varIds0 e1
                |> Result.andThen
                    (\( unusedId1, varIds1, e1_ ) ->
                        assignIdsHelp unusedId1 varIds1 e2
                            |> Result.map
                                (\( unusedId2, varIds2, e2_ ) ->
                                    ( unusedId2
                                    , varIds2
                                    , TyPlus e1_ e2_
                                    )
                                )
                    )

        Lambda arg body ->
            assignIdsHelp unusedId0 varIds0 body
                |> Result.andThen
                    (\( unusedId1, varIds1, body_ ) ->
                        Dict.get arg varIds1
                            |> Result.fromMaybe (UnboundName arg)
                            |> Result.map
                                (\argId ->
                                    ( unusedId1
                                    , varIds1
                                    , TyLambda arg body_ argId
                                    )
                                )
                    )
    )
        |> Result.map
            (\( unusedIdN, varIdsN, recursedExpr ) ->
                ( unusedIdN + 1
                , varIdsN
                , ( recursedExpr, TVar unusedIdN )
                )
            )



-- STAGE 2: Generate equations between types (apply type inference rules)


{-| We can add a third element - the original node: TypedExpr, for debugging
-}
type alias TypeEquation =
    ( Type, Type )


eq : Type -> Type -> TypeEquation
eq t1 t2 =
    ( t1, t2 )


generateEquations : TypedExpr -> List TypeEquation
generateEquations ( expr, type_ ) =
    case expr of
        TyInt _ ->
            [ eq type_ TInt ]

        TyVar _ ->
            []

        TyPlus ( e1, t1 ) ( e2, t2 ) ->
            let
                eqs1 =
                    generateEquations ( e1, t1 )

                eqs2 =
                    generateEquations ( e2, t2 )
            in
            -- for (a + b):
            [ eq t1 TInt -- type of a is Int
            , eq t2 TInt -- type of b is Int
            , eq type_ TInt -- type of (a + b) is Int
            ]
                ++ eqs1
                ++ eqs2

        TyLambda _ ( body, bodyType ) argId ->
            let
                eqsBody =
                    generateEquations ( body, bodyType )
            in
            -- type of (\arg -> body) is (arg -> body)
            eq type_ (TFunction (TVar argId) bodyType)
                :: eqsBody



{- STAGE 3: find the most general unifier (solution) for the equations

   Keywords:
   - Union-find
   - Huet's algorithm
   - Unification
   - Most general unifier
-}


type alias Subst =
    Dict Int Type


unifyAllEquations : List TypeEquation -> Result TypeError Subst
unifyAllEquations equations =
    List.foldl
        (\( t1, t2 ) subst -> Result.andThen (unify t1 t2) subst)
        (Ok Dict.empty)
        equations


unify : Type -> Type -> Subst -> Result TypeError Subst
unify t1 t2 subst =
    if t1 == t2 then
        Ok subst

    else
        case ( t1, t2 ) of
            ( TVar id, _ ) ->
                unifyVariable id t2 subst

            ( _, TVar id ) ->
                unifyVariable id t1 subst

            ( TFunction arg1 result1, TFunction arg2 result2 ) ->
                unify result1 result2 subst
                    |> Result.andThen (unify arg1 arg2)

            _ ->
                Err (CannotUnify t1 t2)


unifyVariable : Int -> Type -> Subst -> Result TypeError Subst
unifyVariable id type_ subst =
    case Dict.get id subst of
        Just typeForId ->
            unify typeForId type_ subst

        Nothing ->
            case
                getVarId type_
                    |> Maybe.andThen (\id2 -> Dict.get id2 subst)
                    |> Maybe.map (\typeForId2 -> unify (TVar id) typeForId2 subst)
            of
                Just newSubst ->
                    newSubst

                Nothing ->
                    if occurs id type_ subst then
                        Err (VarOccursInType id type_)

                    else
                        Ok (Dict.insert id type_ subst)


occurs : Int -> Type -> Subst -> Bool
occurs id type_ subst =
    if type_ == TVar id then
        True

    else
        case
            getVarId type_
                |> Maybe.andThen (\id2 -> Dict.get id2 subst)
                |> Maybe.map (\typeForId2 -> occurs id typeForId2 subst)
        of
            Just doesOccur ->
                doesOccur

            Nothing ->
                case type_ of
                    TFunction arg result ->
                        occurs id result subst
                            || occurs id arg subst

                    _ ->
                        False


getType : Type -> Subst -> Type
getType type_ subst =
    -- TODO rename types afterwards?
    if Dict.isEmpty subst then
        type_

    else
        case type_ of
            TInt ->
                type_

            TVar id ->
                Dict.get id subst
                    |> Maybe.map (\typeForId -> getType typeForId subst)
                    |> Maybe.withDefault type_

            TFunction arg result ->
                TFunction
                    (getType arg subst)
                    (getType result subst)
