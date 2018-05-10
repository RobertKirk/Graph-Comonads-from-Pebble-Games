module TestExamples
import Data.Fin
import Prelude.Strings
import src.ProofHelpers
import src.NonEmptyList
import src.NonEmptyStream

import src.RCategories
import src.Graphs
import src.PebbleComonad

%default total

--RCategories Tests
arr : Type -> Type -> Type
arr t1 t2 = t1 -> t2

TypeCategory : RCategory Type
TypeCategory = RCategoryInfo arr id (.)

nonEmptyListFunctor : RFunctor Type TypeCategory
nonEmptyListFunctor = RFunctorInfo NEList map

nonEmptyListComonad : RComonad Type TypeCategory
nonEmptyListComonad = RComonadInfo nonEmptyListFunctor NonEmptyList.head Singl

data LessThanEqual : Nat -> Nat -> Type where
    IsLessThanEqual : (n : Nat) -> (m : Nat) -> LTE n m -> LessThanEqual n m

lteId : LessThanEqual n n
lteId = IsLessThanEqual n n (lteRefl)

lteComp : LessThanEqual b c -> LessThanEqual a b -> LessThanEqual a c
lteComp (IsLessThanEqual b c prfbc) (IsLessThanEqual a b prfab) = IsLessThanEqual a c (lteTransitive prfab prfbc)

POSetCategory : RCategory Nat
POSetCategory = RCategoryInfo LessThanEqual lteId lteComp

ltZimpliesZ : LTE x Z -> x = Z
ltZimpliesZ (LTEZero) = Refl
ltZimpliesZ (LTESucc prf) impossible

mult2 : Nat -> Nat
mult2 Z = Z
mult2 (S n) = S (S (mult2 n))

mult2Map : LessThanEqual a b -> LessThanEqual (mult2 a) (mult2 b)
mult2Map (IsLessThanEqual a b prfab) = IsLessThanEqual (mult2 a) (mult2 b) (prf a b prfab)
    where prf : (x : Nat) -> (y : Nat) -> LTE x y -> LTE (mult2 x) (mult2 y)
          prf Z y prfxy = LTEZero
          prf x Z prfxy = rewrite ltZimpliesZ prfxy in LTEZero
          prf (S n) (S m) prfxy = let rec = prf n m (fromLteSucc prfxy) in LTESucc (LTESucc rec)

mult2Functor : RFunctor Nat POSetCategory
mult2Functor = RFunctorInfo mult2 mult2Map

-- Graph Tests
lt : Rel Nat
lt (a,b) = a < b

[testEqNat] Eq Nat where
    (==) a b = (toIntegerNat a) - (toIntegerNat b) == 0

NatGraph : Graph
NatGraph = (Nat ** listToNEStream [1,2,3,4,5] ** lt ** testEqNat)

ltchar : Rel Char
ltchar (n,m) = toNat n < toNat m

[testEqString] Eq Char where
    (==) n m = (toNat n) == (toNat m)

Char' : Type
Char' = Char

CharGraph : Graph
CharGraph = (Char' ** listToNEStream ['1','2','3','4','5'] ** ltchar ** testEqString)

testGraphMorph : Gmorph CharGraph NatGraph
testGraphMorph = Gmor (toNat) (IsGraphMorphByElem prf)
    where prf : (a : Char) -> (b : Char) -> True = ltchar (a,b) -> True = lt (toNat a, toNat b)
          prf a b prf1 = prf1
