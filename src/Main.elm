module Main exposing (main)

import Dict exposing (Dict)
import IdSource exposing (IdSource)
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
                |> Result.map (Tuple.first >> generateEquations)
                |> Result.andThen unifyAllEquations
    in
    Result.map2
        (\( ( _, type_ ), _ ) subst ->
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


assignIds : Expr -> Result TypeError ( TypedExpr, IdSource )
assignIds expr =
    assignIdsHelp
        Dict.empty
        IdSource.new
        expr


assignIdsHelp : Dict String Type -> IdSource -> Expr -> Result TypeError ( TypedExpr, IdSource )
assignIdsHelp symbolTable idSource expr =
    case expr of
        Int int ->
            Ok ( ( TyInt int, TInt ), idSource )

        Var name ->
            Dict.get name symbolTable
                |> Result.fromMaybe (UnboundName name)
                |> Result.map (\type_ -> ( ( TyVar name, type_ ), idSource ))

        Plus e1 e2 ->
            assignIdsHelp symbolTable idSource e1
                |> Result.andThen
                    (\( e1_, idSource1 ) ->
                        assignIdsHelp symbolTable idSource1 e2
                            |> Result.map
                                (\( e2_, idSource2 ) ->
                                    let
                                        ( id, idSource3 ) =
                                            IdSource.produceId idSource2
                                    in
                                    ( ( TyPlus e1_ e2_, TVar id ), idSource3 )
                                )
                    )

        Lambda arg body ->
            let
                ( lambdaId, idSource1 ) =
                    IdSource.produceId idSource

                ( argId, idSource2 ) =
                    IdSource.produceId idSource1

                bodySymbolTable =
                    Dict.insert arg (TVar argId) symbolTable
            in
            assignIdsHelp bodySymbolTable idSource2 body
                |> Result.map
                    (\( body_, idSource3 ) ->
                        ( ( TyLambda arg body_ argId, TVar lambdaId ), idSource3 )
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
