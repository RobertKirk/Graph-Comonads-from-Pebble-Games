module Graphs
import src.ProofHelpers
import src.NonEmptyStream
import src.NonEmptyList
import Data.Fin

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
    Gmor : (f: t1 -> t2) -> IsGraphMorph f e1 e2 -> Gmorph (t1 ** v1 ** e1 ** eq1) (t2 ** v2 ** e2 ** eq2)

GidProof : (es : Rel t) -> (a, b : t) -> True = es (a, b) -> True = es (Basics.id a, Basics.id b)
GidProof es a b eqprf1 = eqprf1

Gid : Gmorph a a
Gid {a = (t ** vs ** es ** eq)} = Gmor Basics.id (IsGraphMorphByElem (GidProof es))

infixr 9 ..

compProof : (f1 : ta -> tb) -> (f2 : tb -> tc) -> (eas : Rel ta) -> (ebs : Rel tb) -> (ecs : Rel tc) ->
    IsGraphMorph f1 eas ebs -> IsGraphMorph f2 ebs ecs ->    
    (x, y: ta) -> True = eas (x, y) -> True = ecs ((f2 . f1) x, (f2 . f1) y)
compProof vmap1 vmap2 eas ebc ecs (IsGraphMorphByElem aToBEqPrf) (IsGraphMorphByElem bToCEqPrf) x y eqprf1 =
    bToCEqPrf (vmap1 x) (vmap1 y) (aToBEqPrf x y eqprf1)

(..) : Gmorph b c -> Gmorph a b -> Gmorph a c
(..) {a = (ta ** vas ** eas ** eqa)} {b = (tb ** vbs ** ebs ** eqb)} {c = (tc ** vcs ** ecs ** eqc)} 
    (Gmor vmap2 (IsGraphMorphByElem bToCEqPrf)) (Gmor vmap1 (IsGraphMorphByElem aToBEqPrf)) =
    Gmor (vmap2 . vmap1) (IsGraphMorphByElem (compProof vmap1 vmap2 eas ebs ecs (IsGraphMorphByElem aToBEqPrf) (IsGraphMorphByElem bToCEqPrf)))
        where prf : (x : ta) -> (y : ta) -> True = eas (x, y) -> True = ecs ((vmap2 . vmap1) x, (vmap2 . vmap1) y)
              prf x y eqprf1 = bToCEqPrf (vmap1 x) (vmap1 y) (aToBEqPrf x y eqprf1)

GraphCat : RCategory Graph 
GraphCat = RCategoryInfo Gmorph Gid (..)

-- Now definitions for a Category of a signature with only Binary relations
Signature : Type
Signature = Nat            

Interpretation : Signature -> Type -> Type
Interpretation sig t = (Fin sig) -> (Rel t)

Structure : Signature -> Type
Structure sig =
    DPair Type $ \t =>
    DPair (NEStream t) $ \vs =>
    DPair (Interpretation sig t) $ \es =>
    Eq t

data IsStructureMorph : (sig : Signature) -> (f : t1 -> t2) -> (int1 : Interpretation sig t1) -> (int2 : Interpretation sig t2) -> Type where
    EmptySigStructMorph : sig = 0 -> IsStructureMorph sig f int1 int2
    ItIsStructMorph : ((k : Fin sig) -> IsGraphMorph f (int1 k) (int2 k)) -> IsStructureMorph sig f int1 int2 

data StructMorph : {sig: Signature} -> (a1, a2 : Structure sig) -> Type where
    Smor : (f : t1 -> t2) -> IsStructureMorph sig f int1 int2 -> StructMorph (t1 ** v1 ** int1 ** eq1) (t2 ** v2 ** int2 ** eq2)

SidProof : {sig : Signature} -> (interp : Interpretation sig t) -> IsStructureMorph sig Basics.id interp interp
SidProof {sig = Z}   int = EmptySigStructMorph Refl
SidProof {sig = S k} int = ItIsStructMorph prf
    where prf : (m : Fin (S k)) -> IsGraphMorph Basics.id (int m) (int m)
          prf m = IsGraphMorphByElem (GidProof (int m))

Sid : StructMorph a a
Sid {a = (t ** vs ** rels ** eq)} = Smor Basics.id (SidProof rels)

infixr 9 ./.

(./.) : {sign : Signature} -> StructMorph {sig = sign} b c -> StructMorph {sig = sign} a b -> StructMorph {sig = sign} a c
(./.) {sign = Z}     (Smor f prf1)                       (Smor g prf2)                      = Smor (f . g) (EmptySigStructMorph Refl)
(./.) {sign = (S k)} (Smor f (EmptySigStructMorph Refl)) sm2                                 impossible
(./.) {sign = (S k)} (Smor f2 (ItIsStructMorph f2Prf))   (Smor f (EmptySigStructMorph Refl)) impossible
(./.) {sign = (S k)} {a = (ta ** vas ** arels ** eqa)} {b = (tb ** vbs ** brels ** eqb)} {c = (tc **   vcs ** crels ** eqc)}
    (Smor f2 (ItIsStructMorph f2Prf)) (Smor f1 (ItIsStructMorph f1Prf)) = Smor (f2 . f1) (ItIsStructMorph prf)
        where prf : (n : Fin (S k)) -> IsGraphMorph (f2 . f1) (arels n) (crels n)
              prf n = IsGraphMorphByElem (compProof f1 f2 (arels n) (brels n) (crels n) (f1Prf n) (f2Prf n))

StructCat : (sigma : Signature) -> RCategory (Structure sigma)
StructCat sigma = RCategoryInfo StructMorph Sid (./.)
