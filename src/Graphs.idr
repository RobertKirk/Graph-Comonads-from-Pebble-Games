module Graphs
import src.Categories
import src.ProofHelpers

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
IntGraph = MkG (Nat ** [0,1,2,3,4,5,6,7] ** (\(x,y) => (x<y)))

data IsGraphMorphElem : (f: t1-> t2) -> (x : t1) -> (y : t1) -> (e1 : Rel t1) -> (e2 : Rel t2) -> Type where
    IsGraphMorphElemIsEdge : (IsTrueBool (e1 (x, y))) -> IsTrueBool (e2 (f x, f y)) -> IsGraphMorphElem f x y e1 e2
    IsGraphMorphElemNoEdge : (IsFalseBool (e1 (x, y))) -> IsGraphMorphElem f x y e1 e2

data IsGraphMorph : (f: t1-> t2) -> (xs : List t1) -> (ys : List t2) -> (e1 : Rel t1) -> (e2 : Rel t2) -> Type where
    IsGraphMorphSingleton : IsGraphMorphElem f x y e1 e2 -> IsGraphMorph f [x] [y] e1 e2
    IsGraphMorphCons : IsGraphMorphElem f x y e1 e2 -> IsGraphMorph f xs ys e1 e2 -> IsGraphMorph f (x::xs) (y::ys) e1 e2
    BelieveMeGM : IsGraphMorph f xs ys e1 e2

data Gmorph : (g1 : Graph) -> (g2 : Graph) -> Type where
    Gmor : (f: t1 -> t2) -> map f v1 = v2 -> IsGraphMorph f v1 (map f v1) e1 e2 -> Gmorph (MkG (t1 ** v1 ** e1)) (MkG (t2 ** v2 ** e2))

-- Gapp : Gmorph (MkG (t1 ** v1 ** e1)) (MkG (t2 ** v2 ** e2)) -> Graph
-- Gapp (Gmor vmap emap) = 
--     MkG (t2 ** (map vmap v1) ** (\p =>
--         elem p edges
--             where edges = map (\(x,y) => (vmap x, vmap y)) (filter (emap . e1) [(x,y) | x <- v1, y <- v1])
--     ))

graphIdIsMorphism : (xs : List t) -> (es : Rel t) -> IsGraphMorph Basics.id xs xs es es
graphIdIsMorphism [x] es =  if (es (x, x)) then IsGraphMorphSingleton (IsGraphMorphElemIsEdge (IsTrue (es (x, x))) (IsTrue (es (id x, id x))))
                            else IsGraphMorphSingleton (IsGraphMorphElemNoEdge (IsFalse (es (x, x))))
graphIdIsMorphism (x::xs) es = let rec = graphIdIsMorphism xs es in 
                                if (es (x, x)) then IsGraphMorphCons (IsGraphMorphElemIsEdge (IsTrue (es (x, x))) (IsTrue (es (id x, id x)))) rec
                                else IsGraphMorphCons (IsGraphMorphElemNoEdge (IsFalse (es (x, x)))) rec
                            
Gid : Gmorph a a
Gid {a = (MkG (t ** vs ** es))} = Gmor Basics.id (mapIdIsId vs) (rewrite mapIdIsId vs in (graphIdIsMorphism vs es))

infixr 9 ..

(..) : Gmorph b c -> Gmorph a b -> Gmorph a c
(..) {a = (MkG (ta ** vas ** eas))} {b = (MkG (tb ** vbs ** ebs))} {c = (MkG (tc ** vcs ** ecs))} 
    (Gmor vmap2 vmap2IsMappedList vmap2IsGraphMorph) (Gmor vmap1 vmap1IsMappedList vmap1IsGraphMorph) =
    Gmor (vmap2 . vmap1) (believe_me True)  BelieveMeGM

Category Gmorph where
    id = Gid
    (.) = (..)


{- 
    (replace (sym (mapFusion vmap2 vmap1 vas))
        (rewrite vmap2IsMappedList in Refl))

    (rewrite vmap1IsMappedList in rewrite vmap2IsMappedList in (sym mapFusion vmap2 vmap1 vas))
-}