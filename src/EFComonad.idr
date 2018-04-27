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
    MkPlays : (k : Fin (S n)) -> {auto ok : IsFSucc k} -> Vect (finToNat k) t -> EFplaysType n t

Uninhabited (EFplaysType Z t) where
    uninhabited (MkPlays FZ {ok = ItIsFSucc} xs) impossible
    uninhabited (MkPlays (FS k) {ok = p} xs) impossible

efWeaken : EFplaysType n t -> EFplaysType (S n) t
efWeaken (MkPlays FZ {ok = IsFSucc} xs) impossible
efWeaken (MkPlays (FS j) {ok = p}   xs) = MkPlays (FS (weaken j)) (rewrite sym (weakenPreservesToNat (FS j)) in xs)

efWeakenN : (m : Nat) -> EFplaysType n t -> EFplaysType (n + m) t
efWeakenN m (MkPlays FZ {ok = IsFSucc} xs) impossible
efWeakenN m (MkPlays (FS j) {ok = p} xs) = MkPlays (FS (weakenN m j)) (rewrite sym (weakenNPreservesToNat m (FS j)) in xs)

[EFplaysTypeEq] Eq t => Eq (EFplaysType n t) where
    (==) (MkPlays k xs) (MkPlays j ys) = k == j && toList xs == toList ys

initial :  NEStream t -> NEStream (EFplaysType 1 t)
initial xs = map (\x => MkPlays (FS FZ) [x]) xs

uplength : NEStream t -> (n : Nat) -> NEStream (EFplaysType n t) -> NEStream (EFplaysType (S n) t)
uplength xs n plays = concatNESofNES (map (\(MkPlays len play) => (map (\el => MkPlays (FS len) (el::play)) xs)) plays)

efplays : (bound : Nat) -> {auto ok : IsSucc bound} -> NEStream t -> NEStream (EFplaysType bound t)
efplays Z {ok = ItIsSucc}  xs impossible
efplays (S Z) {ok = p}     xs = initial xs
efplays (S (S k)) {ok = p} xs = myIt 1 (LTESucc (LTESucc LTEZero)) (uplength xs) (initial xs)
    where myIt : (start : Nat) -> LTE (S start) (S (S k)) -> ((n : Nat) -> NEStream (EFplaysType n t) -> NEStream (EFplaysType (S n) t)) -> 
            NEStream (EFplaysType start t) -> NEStream (EFplaysType (S (S k)) t)
          myIt start LTEZero f xs impossible
          myIt start (LTESucc startLTProof) f xs with (isLTE (S start) (S k)) proof p
            | Yes prfSStart = ap (rewrite sym (plusMinusProof start (S (S k)) (lteSuccRight startLTProof)) in 
                                (map (efWeakenN ((-) {smaller = lteSuccLeft ((LTESucc startLTProof))} (S (S k)) start)) xs))
                                (assert_total (myIt (S start) (LTESucc prfSStart) f (f start xs)))
            | No contra = ap (map efWeaken (rewrite sym (lteToEqual start (S k) (startLTProof) (\p => contra p)) in xs))
                            (rewrite sym (lteToEqual (S start) (S (S k)) (LTESucc startLTProof) (\(LTESucc p) => contra p)) in (f start xs))

efRelPrefix : Eq t => Vect j t -> Vect k t -> Bool
efRelPrefix {j = n} {k = m}xs ys with (isLTE n m)
    | Yes prf = isPrefixOf xs ys
    | No contra = isPrefixOf ys xs

efRel : Eq t => Rel t -> Rel (EFplaysType bound t)
efRel r ((MkPlays FZ {ok = ItIsFSucc {k = FZ}} xs), (MkPlays FZ {ok = ItIsFSucc} ys)) impossible
efRel r (p1, (MkPlays FZ {ok = ItIsFSucc} ys)) impossible
efRel r ((MkPlays (FS j) {ok = pj} xs), (MkPlays (FS k) {ok = pk} ys)) = r ((Vect.last xs), (Vect.last ys)) && efRelPrefix xs ys

efInterp : Eq t => (bound : Nat) -> (int : Interpretation sig t) -> Interpretation sig (EFplaysType bound t)
efInterp bound int rel = efRel (int rel)

EFComonadObj : (bound : Nat) -> {auto ok : IsSucc bound} -> Structure sig -> Structure sig
EFComonadObj Z {ok = ItIsSucc} strut impossible
EFComonadObj (S k) {ok = p} (t ** vs ** interp ** eqt) =
    (EFplaysType (S k) t **
    efplays (S k) vs **
    efInterp (S k) interp **
    EFplaysTypeEq)

-- EFComonadMorph : (bound : Nat) -> {auto ok : IsSucc bound} -> StructMorph s1 s2 -> StructMorph (EFComonadObj bound s1) (EFComonadObj bound s2)
-- EFComonadMorph Z {ok = ItIsSucc} smorph impossible
-- EFComonadMorph (S k) {ok = p} (Smor f prf) = ?holeMorph

-- EFFunctor : (bound : Nat) -> {auto ok : IsSucc bound} -> RFunctor (Structure sigma) (StructCat sigma)
-- EFFunctor Z {ok = ItIsSucc} impossible
-- EFFunctor (S k) {ok = p} = RFunctorInfo (EFComonadObj (S k)) (EFComonadMorph (S k))

counitFunc : EFplaysType (S k) t -> t
counitFunc (MkPlays FZ {ok = ItIsFSucc} xs) impossible
counitFunc (MkPlays (FS j) {ok = p} xs) = last xs

counitEF : {sigma : Signature} -> {s : Structure sigma} -> (bound : Nat) -> {auto ok : IsSucc bound} -> StructMorph (EFComonadObj bound s) s
counitEF {sigma = sig} Z {ok = ItIsSuc} impossible
counitEF {sigma = Z}   {s = (t ** vs ** interp ** eqt)} (S k) {ok = p} = Smor EFComonad.counitFunc (EmptySigStructMorph Refl)
counitEF {sigma = (S sig)} {s = (t ** vs ** interp ** eqt)} (S k) {ok = p} = Smor EFComonad.counitFunc (ItIsStructMorph prf)
    where   intprf : (a, b : EFplaysType (S k) t) -> True = efRel r (a, b) -> True = r (counitFunc a, counitFunc b)
            intprf (MkPlays FZ {ok = ItIsFSucc} xs) p proof1 impossible
            intprf q (MkPlays FZ {ok = ItIsFSucc} xs) proof1 impossible
            intprf (MkPlays (FS lx) {ok = p} xs) (MkPlays (FS ly) {ok = q} ys) proof1 = andTrueImpliesConjunctsTrueL proof1
            prf : (rel : Fin (S sig)) -> IsGraphMorph EFComonad.counitFunc (efInterp (S k) interp rel) (interp rel)
            prf rel = IsGraphMorphByElem intprf

morphExtend : (EFplaysType (S j) t1 -> t2) -> EFplaysType (S j) t1 -> EFplaysType (S j) t2
morphExtend morph (MkPlays FZ {ok = ItIsFSucc} xs) impossible
morphExtend morph (MkPlays (FS k) {ok = p}    xs) = MkPlays (FS k) {ok = p} (map morph (playInits xs))
    where   playInits : Vect (finToNat (FS k)) t -> Vect (finToNat (FS k)) (EFplaysType (S j) t)
            playInits plays = ?hole --map (\(l ** ps) => MkPlays (natToFin l (finToNat (FS k)) {ok = (believe_me _)}) {ok = (believe_me _)} (rewrite vectInj (finToNatToFin l (FS k) (believe_me True)) in ps)) (vectorsInits plays)

coextensionEF : {sigma : Signature} -> {s1, s2 : Structure sigma} -> (bound : Nat) -> {auto ok : IsSucc bound} -> 
    StructMorph (EFComonadObj bound s1) s2 -> StructMorph (EFComonadObj bound s1) (EFComonadObj bound s2)
coextensionEF Z {ok = ItIsSucc} morph impossible
coextensionEF {sigma = Z} {s1 = (t1 ** vs1 ** interp1 ** eqt1)} {s2 = (t2 ** vs2 ** interp2 ** eqt2)} (S j) {ok = p} (Smor morph prof) = Smor (morphExtend morph) (EmptySigStructMorph Refl)
coextensionEF {sigma = S sig} (S j) {ok = p} morph = ?coext2 -- Smor morphExtend (ItIsStructMorph prf)
--     where   prf = ?prf
--             morphExtend = ?mext1

EFIndexedComonadKleisli : {sigma : Signature} -> RIxCondComonadKleisli (Structure sigma) (StructCat sigma) Nat IsSucc
EFIndexedComonadKleisli = RIxCondComonadKleisliInfo EFComonadObj counitEF coextensionEF
