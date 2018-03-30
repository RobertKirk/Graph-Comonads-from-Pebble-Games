module Graphs
import src.ProofHelpers

import src.RCategories

%access public export
%default total

Rel : Type -> Type
Rel t = (t,t) -> Bool

Graph : Type
Graph =
    DPair Type $ \v =>
    DPair (List v) $ \vs =>
    DPair (Rel v) $ \es =>
    Eq v

data IsGraphMorphElem : (f: t1-> t2) -> (x : t1) -> (y : t1) -> (e1 : Rel t1) -> (e2 : Rel t2) -> Type where
    IsGraphMorphElemIsEdge : (IsTrueBool (e1 (x, y))) -> IsTrueBool (e2 (f x, f y)) -> IsGraphMorphElem f x y e1 e2
    IsGraphMorphElemNoEdge : (IsFalseBool (e1 (x, y))) -> IsGraphMorphElem f x y e1 e2

data IsGraphMorph : (f: t1-> t2) -> (xs : List t1) -> (ys : List t2) -> (e1 : Rel t1) -> (e2 : Rel t2) -> Type where
    IsGraphMorphEmpty : IsGraphMorph f [] [] e1 e2
    IsGraphMorphSingleton : IsGraphMorphElem f x y e1 e2 -> IsGraphMorph f [x] [y] e1 e2
    IsGraphMorphCons : IsGraphMorphElem f x y e1 e2 -> IsGraphMorph f xs ys e1 e2 -> IsGraphMorph f (x::xs) (y::ys) e1 e2
    BelieveMeGM : IsGraphMorph f xs ys e1 e2

graphIdIsMorphism : (xs : List t) -> (es : Rel t) -> IsGraphMorph Basics.id xs xs es es
graphIdIsMorphism [] es = IsGraphMorphEmpty
graphIdIsMorphism [x] es =  if (es (x, x)) then IsGraphMorphSingleton (IsGraphMorphElemIsEdge (IsTrue (es (x, x))) (IsTrue (es (id x, id x))))
                            else IsGraphMorphSingleton (IsGraphMorphElemNoEdge (IsFalse (es (x, x))))
graphIdIsMorphism (x::xs) es = let rec = graphIdIsMorphism xs es in 
                                if (es (x, x)) then IsGraphMorphCons (IsGraphMorphElemIsEdge (IsTrue (es (x, x))) (IsTrue (es (id x, id x)))) rec
                                else IsGraphMorphCons (IsGraphMorphElemNoEdge (IsFalse (es (x, x)))) rec

data Gmorph : (g1 : Graph) -> (g2 : Graph) -> Type where
    Gmor : (f: t1 -> t2) -> map f v1 = v2 -> IsGraphMorph f v1 (map f v1) e1 e2 -> (Gmorph (t1 ** v1 ** e1 ** eq1) (t2 ** v2 ** e2 ** eq2))

Gid : Gmorph a a
Gid {a = (t ** vs ** es ** eq)} = Gmor Basics.id (mapIdIsId vs) (rewrite mapIdIsId vs in (graphIdIsMorphism vs es))

infixr 9 ..

(..) : Gmorph b c -> Gmorph a b -> Gmorph a c
(..) {a = (ta ** vas ** eas ** eqa)} {b = (tb ** vbs ** ebs ** eqb)} {c = (tc ** vcs ** ecs ** eqc)} 
    (Gmor vmap2 vmap2IsMappedList vmap2IsGraphMorph) (Gmor vmap1 vmap1IsMappedList vmap1IsGraphMorph) =
    Gmor (vmap2 . vmap1) (intermediateMapsCompose vmap1 vmap2 vas vbs vcs vmap1IsMappedList vmap2IsMappedList) BelieveMeGM

GraphCat : RCategory Graph 
GraphCat = RCategoryInfo Gmorph Gid (..)

-- Same definitions with data constructor
data Graph' = MkG Graph

data Gmorph' : (g1 : Graph') -> (g2 : Graph') -> Type where
    Gmor' : (f: t1 -> t2) -> map f v1 = v2 -> IsGraphMorph f v1 (map f v1) e1 e2 -> Gmorph' (MkG (t1 ** v1 ** e1 ** eq1)) (MkG (t2 ** v2 ** e2 ** eq2))

Gid' : Gmorph' a a
Gid' {a = (MkG (t ** vs ** es ** eq))} = Gmor' Basics.id (mapIdIsId vs) (rewrite mapIdIsId vs in (graphIdIsMorphism vs es))

comp : Gmorph' b c -> Gmorph' a b -> Gmorph' a c
comp {a = (MkG (ta ** vas ** eas ** eqa))} {b = (MkG (tb ** vbs ** ebs ** eqb))} {c = (MkG (tc ** vcs ** ecs ** eqc))} 
    (Gmor' vmap2 vmap2IsMappedList vmap2IsGraphMorph) (Gmor' vmap1 vmap1IsMappedList vmap1IsGraphMorph) =
    Gmor' (vmap2 . vmap1) (intermediateMapsCompose vmap1 vmap2 vas vbs vcs vmap1IsMappedList vmap2IsMappedList) BelieveMeGM

GraphCat' : RCategory Graph' 
GraphCat' = RCategoryInfo Gmorph' Gid' comp
