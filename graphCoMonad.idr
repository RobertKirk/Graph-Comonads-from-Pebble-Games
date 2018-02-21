module Main

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

-- Gapp : Gmorph g1 (v2 ** _ ** _) -> (g1:Graph) -> Graph
-- Gapp (Gmor vmap emap) (t ** vs ** es) = 
--     (v2 ** (map vmap vs) ** (\(u,v) => )
--     map (\(n,es) => (n, map (\(u,v) => (vmap u, vmap v)) (filter (emap n) es))) ess
--     )

Gid : Gmorph (MkG (t1 ** v1 ** e1)) (MkG (t1 ** v1 ** e1))
Gid = Gmor (\x => x) (\e => True)

infixr 9 ..

-- (..) : Gmorph (v2 ** vs2 ** r2) (v3 ** vs3 ** r3) -> Gmorph (v1 ** vs1 ** r1) (v2 ** vs2** r2) -> Gmorph (v1 ** vs1 ** r1) (v3 ** vs3 ** r3)
(..) : Gmorph b1 c1 -> Gmorph a1 b1 -> Gmorph a1 c1
(..) (Gmor vmap2 emap2) (Gmor vmap1 emap1) =
   Gmor 
    (vmap2 . vmap1)
    (\(t1, t2) => 
        case emap1 (t1, t2) of
            True => emap2 (vmap1 t1, vmap1 t2)
            False => False
    )

interface Category (mor : obj -> obj -> Type) where
    id  : {p:obj} -> mor p p
    (.) : {a:obj} -> {b:obj} -> {c:obj} -> mor b c -> mor a b -> mor a c

-- MyCategory MyGraph where
--     mor = Gmorph
--     id = Gid
--     (.) = (..)

interface Category morph => Functor (morph : obj -> obj -> Type) (f : obj -> obj) | f where
    fmap : morph a b -> morph (f a) (f b)

interface Functor morph m => Monad (morph : obj -> obj -> Type) (m : obj -> obj) | m where
    unit : morph o (m o)
    multiplication : morph (m (m o)) (m o)

interface Functor morph t => Comonad (morph : obj -> obj -> Type) (t : obj -> obj) | m where
    counit : morph (t o) o
    comultiplication : morph (t o) (t (t o))

interface Category morph => IxComonad (morph : obj -> obj -> Type) (t: k -> obj -> obj) where
    ixcounit : morph (t i o) o
    ixcomultiplication : morph (t i o) (t i (t i o))

