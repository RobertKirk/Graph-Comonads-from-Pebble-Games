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

data IsGraphMorph : (f: t1 -> t2) -> (e1 : Rel t1) -> (e2 : Rel t2) -> Type where
    IsGraphMorphByElem : ((a : t1) -> (b : t1) -> True = e1 (a, b) -> True = e2 (f a, f b)) -> IsGraphMorph f e1 e2

-- Note this doesn't require map f v1 = v2, or something similar saying the image of f on g1 lies in g2, 
-- as we can't prove this for infinite lists                        
data Gmorph : (g1 : Graph) -> (g2 : Graph) -> Type where
    Gmor : (f: t1 -> t2) -> IsGraphMorph f e1 e2 -> (Gmorph (t1 ** v1 ** e1 ** eq1) (t2 ** v2 ** e2 ** eq2))

Gid : Gmorph a a
Gid {a = (t ** vs ** es ** eq)} = Gmor Basics.id (IsGraphMorphByElem prf)
                where prf : (a : t) -> (b : t) -> True = es (a, b) -> True = es (Basics.id a, Basics.id b)
                      prf a b eqprf1 = eqprf1

infixr 9 ..

(..) : Gmorph b c -> Gmorph a b -> Gmorph a c
(..) {a = (ta ** vas ** eas ** eqa)} {b = (tb ** vbs ** ebs ** eqb)} {c = (tc ** vcs ** ecs ** eqc)} 
    (Gmor vmap2 (IsGraphMorphByElem bToCEqPrf)) (Gmor vmap1 (IsGraphMorphByElem aToBEqPrf)) =
    Gmor (vmap2 . vmap1) (IsGraphMorphByElem prf)
        where prf : (x : ta) -> (y : ta) -> True = eas (x, y) -> True = ecs ((vmap2 . vmap1) x, (vmap2 . vmap1) y)
              prf x y eqprf1 = bToCEqPrf (vmap1 x) (vmap1 y) (aToBEqPrf x y eqprf1)

-- GmorphEquality : Gmorph g1 g2 -> Gmorph g1 g2 -> Bool
-- GmorphEquality (Gmor f1 prf1) (Gmor f2 prf2) = f1 == f2

GraphCat : RCategory Graph 
GraphCat = RCategoryInfo Gmorph Gid (..)
