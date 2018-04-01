module ProofHelpers
import Data.Fin

import src.NonEmptyStream

%access public export
%default total

data IsTrueBool : Bool -> Type where
    IsTrue : (True : Bool) -> IsTrueBool True

data IsFalseBool : Bool -> Type where
    IsFalse : (False : Bool) -> IsFalseBool False

data IsMappedList : (f: t1 -> t2) -> (xs : List t1) -> (ys : List t2) -> Type where
    IsEmptyMapList : IsMappedList f [] []
    IsConsMapList : IsMappedList f xs ys -> f x = y -> IsMappedList f (x::xs) (y::ys)
    IsFullMapList : map f xs = ys -> IsMappedList f xs ys

data IsElemOfList : (x : t) -> (ys : List t) -> Type where
    IsSingleElemList : IsElemOfList x [x]
    IsConsElemList : Either (x = y) (IsElemOfList x ys) -> IsElemOfList x (y::ys)

mappedListsHaveSameLength : (f : t1 -> t2) -> (xs : List t1) -> (ys : List t2) -> map f xs = ys -> length xs = length ys
mappedListsHaveSameLength f xs ys pf = rewrite sym pf in rewrite mapPreservesLength f xs in Refl

intermediateMapsCompose : (f : t1 -> t2) -> (g: t2 -> t3) -> (xs : List t1) -> 
    (ys : List t2) -> (zs : List t3) -> map f xs = ys -> map g ys = zs -> map (g . f) xs = zs
intermediateMapsCompose f g xs ys zs pf1 pf2 = rewrite sym (mapFusion g f xs) in rewrite pf1 in rewrite pf2 in Refl

data IsSucc : (n : Nat) -> Type where
    ItIsSucc : IsSucc (S n)
  
Uninhabited (IsSucc Z) where
    uninhabited ItIsSucc impossible
  
||| A decision procedure for `IsSucc`
isItSucc : (n : Nat) -> Dec (IsSucc n)
isItSucc Z = No absurd
isItSucc (S n) = Yes ItIsSucc

finUnit : Fin (S k)
finUnit = FZ
