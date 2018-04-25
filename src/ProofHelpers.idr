module ProofHelpers
import Data.Fin
import Data.Vect

import src.NonEmptyList
import src.NonEmptyStream

%access public export
%default total

-- fintonatprf : finToNat (FS FZ) = 1
-- fintonatprf = Refl

-- vectorsInits : Vect n t -> Vect n (p ** Vect (finToNat p) t)
-- vectorsInits Nil = Nil
-- vectorsInits (x::xs) = (rewrite sym fintonatprf in ((FS FZ) ** (x::Nil))) :: map (\(p ** ys) => (FS p ** x::ys)) (vectorsInits xs) 

mappedListsHaveSameLength : (f : t1 -> t2) -> (xs : List t1) -> (ys : List t2) -> map f xs = ys -> length xs = length ys
mappedListsHaveSameLength f xs ys pf = rewrite sym pf in rewrite mapPreservesLength f xs in Refl

intermediateMapsCompose : (f : t1 -> t2) -> (g: t2 -> t3) -> (xs : List t1) -> 
    (ys : List t2) -> (zs : List t3) -> map f xs = ys -> map g ys = zs -> map (g . f) xs = zs
intermediateMapsCompose f g xs ys zs pf1 pf2 = rewrite sym (mapFusion g f xs) in rewrite pf1 in rewrite pf2 in Refl

mapPreservesNonEmpty : (f : a -> b) -> (xs : List a) -> NonEmpty xs -> NonEmpty (map f xs)
mapPreservesNonEmpty f [] IsNonEmpty impossible
mapPreservesNonEmpty f (y::ys) pf = IsNonEmpty

andTrueImpliesConjunctsTrueL : {a : Bool} -> True = a && b -> True = a
andTrueImpliesConjunctsTrueL {a = True}  prf = Refl
andTrueImpliesConjunctsTrueL {a = False} Refl impossible

andIsCommutative : (a : Bool) -> (b : Bool) -> True = a && b -> True = b && a
andIsCommutative False b     Refl impossible
andIsCommutative True  False Refl impossible
andIsCommutative True  True  prf  = Refl

andTrueImpliesConjunctsTrueR : {b : Bool} -> True = a && b -> True = b
andTrueImpliesConjunctsTrueR {a = x} {b = y} prf = andTrueImpliesConjunctsTrueL {a = y} (andIsCommutative x y prf)

andCombines : (a : Bool) -> (b : Bool) -> True = a -> True = b -> True = a && b
andCombines True  True  prfa prfb = Refl
andCombines a     False prfa Refl impossible
andCombines False b     Refl prfb impossible

lastOfMapIsFOfLast : (f : a -> b) -> (xs : NEList a) -> last (map f xs) = f (last xs)
lastOfMapIsFOfLast f (Singl x) = Refl
lastOfMapIsFOfLast f (x:<:xs) = lastOfMapIsFOfLast f xs

sndFuncBehaves1 : (f : t2 -> t3) -> f . snd = snd . (\p => (fst p, f (snd p)))
sndFuncBehaves1 f = Refl

pairCong : (f : (t1,t1) -> Bool) -> a = x -> b = y -> f (a,b) = f (x,y)
pairCong f prf1 prf2 = rewrite prf1 in rewrite prf2 in Refl

ltInjective : (n, m : Nat) -> lt (S n) (S m) = lt n m
ltInjective Z Z     = Refl
ltInjective Z (S k) = Refl
ltInjective (S k) Z = Refl
ltInjective (S k) (S j) = Refl 

ltToLT : (n, m : Nat) -> True = (lt n m) -> LT n m
ltToLT Z     Z     Refl impossible
ltToLT Z     (S k) prf = LTESucc LTEZero
ltToLT (S k) Z Refl impossible
ltToLT (S k) (S j) prf = LTESucc (ltToLT k j prf)

ltImpliesLTE : (n, m : Nat) -> LT n m -> LTE n m
ltImpliesLTE Z Z prf impossible
ltImpliesLTE Z (S k) prf = LTEZero
ltImpliesLTE (S k) Z prf impossible
ltImpliesLTE (S k) (S j) prf = lteSuccLeft prf

compareToLT : (n, m : Nat) ->  LT = compare n m -> LT n m
compareToLT Z     Z     Refl impossible
compareToLT (S k) Z     Refl impossible
compareToLT Z     (S k) prf = LTESucc LTEZero
compareToLT (S k) (S j) prf = LTESucc (compareToLT k j prf)

compareSwap : (n, m : Nat) ->  GT = compare n m -> LT = compare m n
compareSwap Z     Z     Refl impossible
compareSwap Z     (S k) Refl impossible
compareSwap (S k) Z     prf = Refl
compareSwap (S k) (S j) prf = compareSwap k j prf

mapPreservesLengthNel : (f : a -> b) -> (l : NEList a) -> length (map f l) = length l
mapPreservesLengthNel f (Singl x) = Refl
mapPreservesLengthNel f (x:<:xs)  = let inductiveHypothesis = mapPreservesLengthNel f xs in rewrite inductiveHypothesis in Refl

eqReflexiveCompare : (n, m : Nat) -> EQ = compare n m -> EQ = compare m n
eqReflexiveCompare Z Z prf = Refl
eqReflexiveCompare (S k) Z Refl impossible
eqReflexiveCompare Z (S k) Refl impossible
eqReflexiveCompare (S k) (S j) prf = eqReflexiveCompare k j prf

weakenPreservesToNat : (m : Fin k) -> finToNat m = finToNat (weaken m)
weakenPreservesToNat FZ     = Refl
weakenPreservesToNat (FS m) = eqSucc (finToNat m) (finToNat (weaken m)) (weakenPreservesToNat m)

weakenNPreservesToNat : (n : Nat) -> (m : Fin k) -> finToNat m = finToNat (weakenN n m)
weakenNPreservesToNat n FZ     = Refl
weakenNPreservesToNat n (FS m) = eqSucc (finToNat m) (finToNat (weakenN n m)) (weakenNPreservesToNat n m)

plusMinusProof : (n, m : Nat) -> LTE n m -> plus n (m - n) = m
plusMinusProof Z     Z     prf = Refl
plusMinusProof (S k) Z     (LTESucc p) impossible
plusMinusProof (S k) Z     LTEZero impossible 
plusMinusProof Z     (S k) prf = Refl
plusMinusProof (S k) (S j) LTEZero impossible
plusMinusProof (S k) (S j) (LTESucc p) = eqSucc (plus k (minus j k)) j (plusMinusProof k j p)

lteToEqual : (n, m : Nat) -> LTE n m -> Not (LTE (S n) m) -> n = m
lteToEqual Z Z prf1 prf2 = Refl
lteToEqual (S k) Z LTEZero prf2 impossible
lteToEqual (S k) Z (LTESucc p) prf2 impossible
lteToEqual Z (S k) LTEZero prf2 = void (prf2 (LTESucc LTEZero))
lteToEqual (S k) (S j) (LTESucc p) prf2 = eqSucc k j (lteToEqual k j p (prf2 . LTESucc))
