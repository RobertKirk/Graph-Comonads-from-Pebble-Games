module Graphs
import src.Categories

%access public export

Rel : Type -> Type
Rel t = (t,t) -> Bool

Graph' : Type
Graph' =
    DPair Type $ \v =>
    DPair (List v) $ \vs =>
    Rel v

data Graph = MkG Graph'

IntGraph : Graph
IntGraph = MkG (Nat ** [0,1,2,3,4,5,6,7] ** (\(x,y) => x<y))

data Gmorph : Graph -> Graph -> Type where
    Gmor : (t1 -> t2) -> ((t1,t1) -> Bool) -> Gmorph (MkG (t1 ** v1 ** e1)) (MkG (t2 ** v2 ** e2))

-- Gapp : Gmorph (MkG (t1 ** v1 ** e1)) (MkG (t2 ** v2 ** e2)) -> Graph
-- Gapp (Gmor vmap emap) = 
--     MkG (t2 ** (map vmap v1) ** (\p =>
--         elem p edges
--             where edges = map (\(x,y) => (vmap x, vmap y)) (filter (emap . e1) [(x,y) | x <- v1, y <- v1])
--     ))

Gid : Gmorph a a
Gid {a = (MkG (t ** v ** es))} = Gmor (\x => x) (\e => True)

infixr 9 ..

(..) : Gmorph b1 c1 -> Gmorph a1 b1 -> Gmorph a1 c1
(..) (Gmor vmap2 emap2) (Gmor vmap1 emap1) =
   Gmor 
    (vmap2 . vmap1)
    (\(t1, t2) => 
        case emap1 (t1, t2) of
            True => emap2 (vmap1 t1, vmap1 t2)
            False => False
    )

Category Gmorph where
    id = Gid
    (.) = (..)