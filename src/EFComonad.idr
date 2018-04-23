module EFComonad
import Data.Fin
import Data.Vect
import src.ProofHelpers
import src.NonEmptyStream
import src.NonEmptyList

import src.RCategories
import src.Graphs

%access public export
%default total

data IsFSucc : Fin k -> Type where
    ItIsFSucc : IsFSucc (FS k)

data EFplaysType : (n: Nat) -> (t : Type) -> Type where
    MkPlay : (k : Fin (S n)) -> {auto ok : IsFSucc k} -> Vect (finToNat k) t -> EFplaysType n t

efWeaken : EFplaysType n t -> EFplaysType (S n) t
efWeaken (MkPlay FZ {ok = IsFSucc} xs) impossible
efWeaken (MkPlay (FS j) {ok = p}   xs) = MkPlay (FS (weaken j)) (rewrite sym (weakenPreservesToNat (FS j)) in xs)

efWeakenN : (m : Nat) -> EFplaysType n t -> EFplaysType (n + m) t
efWeakenN m (MkPlay FZ {ok = IsFSucc} xs) impossible
efWeakenN m (MkPlay (FS j) {ok = p} xs) = MkPlay (FS (weakenN m j)) (rewrite sym (weakenNPreservesToNat m (FS j)) in xs)

[EFplaysTypeEq] Eq t => Eq (EFplaysType n t) where
    (==) (MkPlay k xs) (MkPlay j ys) = k == j && toList xs == toList ys

initial :  NEStream t -> NEStream (EFplaysType 1 t)
initial xs = map (\x => MkPlay (FS FZ) [x]) xs

uplength : NEStream t -> (n : Nat) -> NEStream (EFplaysType n t) -> NEStream (EFplaysType (S n) t)
uplength xs n plays = concatNESofNES (map (\(MkPlay len play) => (map (\el => MkPlay (FS len) (el::play)) xs)) plays)

efplays : (bound : Nat) -> {auto ok : IsSucc bound} -> NEStream t -> NEStream (EFplaysType bound t)
efplays Z {ok = ItIsSucc}  xs impossible
efplays (S Z) {ok = p}     xs = initial xs
efplays (S (S k)) {ok = p} xs = assert_total (myIt 1 (LTESucc (LTESucc LTEZero)) (uplength xs) (initial xs))
    where myIt : (start : Nat) -> LTE (S start) (S (S k)) -> ((n : Nat) -> NEStream (EFplaysType n t) -> NEStream (EFplaysType (S n) t)) -> 
            NEStream (EFplaysType start t) -> NEStream (EFplaysType (S (S k)) t)
          myIt start LTEZero f xs impossible
          myIt start (LTESucc startLTProof) f xs with (isLTE (S start) (S k)) proof p
            | Yes prfSStart = ap (rewrite sym (plusMinusProof start (S (S k)) (lteSuccRight startLTProof)) in 
                                (map (efWeakenN ((-) {smaller = lteSuccLeft ((LTESucc startLTProof))} (S (S k)) start)) xs))
                                (myIt (S start) (LTESucc prfSStart) f (f start xs))
            | No contra = rewrite sym (lteToEqual (S start) (S (S k)) (LTESucc startLTProof) (\(LTESucc p) => contra p)) in (f start xs)

efRel : Eq t => Rel t -> Rel (EFplaysType pebs t)
efRel r (MkPlay FZ {ok = ItIsFSucc} xs) (MkPlay FZ {ok = ItIsFSucc} ys) impossible
efRel r p1 (MkPlay FZ {ok = ItIsFSucc} ys) impossible
efRel r (MkPlay (FS j) {ok = p} xs) (MkPlay (FS k) {ok = p} xs) = ?hoel

efInterp : Eq t => (bound : Nat) -> (int : Interpretation sig t) -> Interpretation sig (EFplaysType bound t)
efInterp bound int rel = efRel (int rel)

EFComonadObj : (bound : Nat) -> {auto ok : IsSucc bound} -> Structure sig -> Structure sig
EFComonadObj Z {ok = ItIsSucc} strut impossible
EFComonadObj (S k) {ok = p} (t ** vs ** interp ** eqt) =
    (EFplaysType (S k) t **
    efplays (S k) vs **
    efInterp (S k) interp **
    EFplaysTypeEq)

EFComonadMorph : (bound : Nat) -> {auto ok : IsSucc bound} -> StructMorph s1 s2 -> StructMorph (EFComonadObj bound s1) (EFComonadObj bound s2)
EFComonadMorph Z {ok = ItIsSucc} smorph impossible
EFComonadMorph (S k) {ok = p} (Smor f prf) = ?hole23

EFFunctor : (bound : Nat) -> {auto ok : IsSucc bound} -> RFunctor (Structure sigma) (StructCat sigma)
EFFunctor Z {ok = ItIsSucc} impossible
EFFunctor (S k) {ok = p} = RFunctorInfo (EFComonadObj (S k)) (EFComonadMorph (S k))
