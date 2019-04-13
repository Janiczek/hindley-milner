module IdSource exposing (IdSource, new, produceId)


type IdSource =
    IdSource Int
    

new : IdSource
new =
    IdSource 0

produceId : IdSource -> ( Int, IdSource )
produceId (IdSource unusedId) =
    ( unusedId
    , IdSource (unusedId + 1)
    )
