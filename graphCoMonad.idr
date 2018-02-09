module Main
import Control.Category

Rel : Type -> Type
Rel t = (t,t) -> Bool

Graph : Type
Graph =
    DPair Type $ \v =>
    DPair (List v) $ \vs =>
    Rel v

IntGraph : Graph
IntGraph = (Nat ** [0,1,2,3,4,5,6,7] ** (\(x,y) => x==y))

data Gmorph : Graph -> Graph -> Type where
    Gmor : (v1 -> v2) -> ((v1,v1) -> Bool) -> Gmorph (v1 ** _) (v2 ** _)

Gapp : Gmorph g1 (v2 ** _ ** _) -> (g1:Graph) -> Graph
-- Gapp (Gmor vmap emap) (t ** vs ** es) = 
--     (v2 ** (map vmap vs) ** (\(u,v) => )
--     map (\(n,es) => (n, map (\(u,v) => (vmap u, vmap v)) (filter (emap n) es))) ess
--     )


Gid : Gmorph (v1 ** vs1 ** r1) (v1 ** vs1 ** r1)
Gid = Gmor id (\e => True)


infixr 9 ..

(..) : Gmorph (v2 ** vs2 ** r2) (v3 ** vs3 ** r3) -> Gmorph (v1 ** vs1 ** r1) (v2 ** vs2** r2) -> Gmorph (v1 ** vs1 ** r1) (v3 ** vs3 ** r3)
(..) (Gmor vmap2 emap2) (Gmor vmap1 emap1) =
   Gmor 
    (vmap2 . vmap1)
    (\(t1, t2) => 
        case emap1 (t1, t2) of
            True => emap2 (vmap1 t1, vmap1 t2)
            False => False
    )


-- interface MyCategory (obj : Type) where
--     constructor Categ
--     mor : obj -> obj -> Type
--     id  : mor p p
--     (.) : mor u v -> mor t u -> mor t v

-- implementation MyCategory (Graph t) where
--     mor = Gmorph
--     id  = gid
--     (.) = (..)
