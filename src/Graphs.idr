module Graphs
import src.ProofHelpers
import src.NonEmptyStream

import src.RCategories

%access public export
%default total

Rel : Type -> Type
Rel t = (t,t) -> Bool

Graph : Type
Graph =
    DPair Type $ \v =>
    DPair (NEStream v) $ \vs =>
    DPair (Rel v) $ \es =>
    Eq v

data IsGraphMorphElem : (f: t1-> t2) -> (x : t1) -> (y : t1) -> (e1 : Rel t1) -> (e2 : Rel t2) -> Type where
    IsGraphMorphElemIsEdge : (IsTrueBool (e1 (x, y))) -> IsTrueBool (e2 (f x, f y)) -> IsGraphMorphElem f x y e1 e2
    IsGraphMorphElemNoEdge : (IsFalseBool (e1 (x, y))) -> IsGraphMorphElem f x y e1 e2

data IsGraphMorph : (f: t1-> t2) -> (e1 : Rel t1) -> (e2 : Rel t2) -> Type where
    IsGraphMorphByElem : ((a : t1) -> (b : t1) -> IsGraphMorphElem f a b e1 e2) -> IsGraphMorph f e1 e2

graphIdIsMorphism : (es : Rel t) -> IsGraphMorph Basics.id es es
graphIdIsMorphism es = IsGraphMorphByElem prf
        where prf a b = if (es (a,b)) 
                        then IsGraphMorphElemIsEdge (IsTrue (es (a,b))) (IsTrue (es (id a, id b)))
                        else IsGraphMorphElemNoEdge (IsFalse (es (a,b)))

-- note this doesn't require map f v1 = v2, or something similar saying the image of f on g1 lies in g2, 
-- as we can't prove this for infinite lists                        
data Gmorph : (g1 : Graph) -> (g2 : Graph) -> Type where
    Gmor : (f: t1 -> t2) -> IsGraphMorph f e1 e2 -> (Gmorph (t1 ** v1 ** e1 ** eq1) (t2 ** v2 ** e2 ** eq2))

Gid : Gmorph a a
Gid {a = (t ** vs ** es ** eq)} = Gmor id (IsGraphMorphByElem prf)
                where prf a b = if (es (a,b)) 
                    then IsGraphMorphElemIsEdge (IsTrue (es (a,b))) (IsTrue (es (id a, id b)))
                    else IsGraphMorphElemNoEdge (IsFalse (es (a,b)))

infixr 9 ..

(..) : Gmorph b c -> Gmorph a b -> Gmorph a c
(..) {a = (ta ** vas ** eas ** eqa)} {b = (tb ** vbs ** ebs ** eqb)} {c = (tc ** vcs ** ecs ** eqc)} 
    (Gmor vmap2 vmap2IsGraphMorph) (Gmor vmap1 vmap1IsGraphMorph) =
    Gmor (vmap2 . vmap1) (believe_me True)

GraphCat : RCategory Graph 
GraphCat = RCategoryInfo Gmorph Gid (..)
