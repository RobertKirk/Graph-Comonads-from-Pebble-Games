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

initial :  NEList t -> NEList (EFplaysType 1 t)
initial xs = map (\x => MkPlays (FS FZ) [x]) xs

uplength : NEList t -> (n : Nat) -> NEList (EFplaysType n t) -> NEList (EFplaysType (S n) t)
uplength xs n plays = concatNELofNEL (map (\(MkPlays len play) => (map (\el => MkPlays (FS len) (el::play)) xs)) plays)

efplays : (bound : Nat) -> {auto ok : IsSucc bound} -> NEList t -> NEList (EFplaysType bound t)
efplays Z {ok = ItIsSucc}  xs impossible
efplays (S Z) {ok = p}     xs = initial xs
efplays (S (S k)) {ok = p} xs = myIt 1 (LTESucc (LTESucc LTEZero)) (uplength xs) (initial xs)
    where myIt : (start : Nat) -> LTE (S start) (S (S k)) -> ((n : Nat) -> NEList (EFplaysType n t) -> NEList (EFplaysType (S n) t)) -> 
            NEList (EFplaysType start t) -> NEList (EFplaysType (S (S k)) t)
          myIt start LTEZero f xs impossible
          myIt start (LTESucc startLTProof) f xs with (isLTE (S start) (S k)) proof p
            | Yes prfSStart = ap (rewrite sym (plusMinusProof start (S (S k)) (lteSuccRight startLTProof)) in 
                                (map (efWeakenN ((-) {smaller = lteSuccLeft ((LTESucc startLTProof))} (S (S k)) start)) xs))
                                (assert_total (myIt (S start) (LTESucc prfSStart) f (f start xs)))
            | No contra = ap (map efWeaken (rewrite sym (lteToEqual start (S k) (startLTProof) (\p => contra p)) in xs))
                            (rewrite sym (lteToEqual (S start) (S (S k)) (LTESucc startLTProof) (\(LTESucc p) => contra p)) in (f start xs))

efRelPrefix : Eq t => Vect j t -> Vect k t -> Bool
efRelPrefix {j = n} {k = m} xs ys with (isLTE n m)
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

efMap : (bound : Nat) -> {auto ok : IsSucc bound} -> (t1 -> t2) -> EFplaysType bound t1 -> EFplaysType bound t2
efMap Z {ok = ItIsSucc} morph xs impossible
efMap (S k) {ok = p}    morph (MkPlays l xs) = MkPlays l (map morph xs)

EFComonadMorph : (bound : Nat) -> {auto ok : IsSucc bound} -> StructMorph s1 s2 -> StructMorph (EFComonadObj bound s1) (EFComonadObj bound s2)
EFComonadMorph Z {ok = ItIsSucc} smorph impossible
EFComonadMorph (S k) {ok = p} (Smor f prf) = Smor (efMap (S k) {ok = p} f) ?prf

EFFunctor : (bound : Nat) -> {auto ok : IsSucc bound} -> RFunctor (Structure sigma) (StructCat sigma)
EFFunctor Z {ok = ItIsSucc} impossible
EFFunctor (S k) {ok = p} = RFunctorInfo (EFComonadObj (S k)) (EFComonadMorph (S k))

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
            intprf (MkPlays (FS lx) {ok = p} xs) (MkPlays (FS ly) {ok = q} ys) proof1 = conjunctsTrueL proof1
            prf : (rel : Fin (S sig)) -> IsGraphMorph EFComonad.counitFunc (efInterp (S k) interp rel) (interp rel)
            prf rel = IsGraphMorphByElem intprf

playInits : (m, n : Nat) -> {auto ok1 : IsSucc m} -> {auto ok2 : IsSucc n} -> Vect n t -> Vect n (EFplaysType m t)
playInits Z n {ok1 = ItIsSucc} xs impossible
playInits (S j) Z {ok1 = p} {ok2 = ItIsSucc} xs impossible
playInits (S j) (S Z) {ok1 = p} {ok2 = q} [x] = [MkPlays (FS FZ) [x]]
playInits (S Z) (S (S k)) {ok1 = p} {ok2 = q} (x ::xs) = (MkPlays (FS FZ) [x]) :: (playInits (S Z) (S k) xs)
playInits (S (S j)) (S (S k)) {ok1 = p} {ok2 = q} (x::xs) = 
    (MkPlays (FS FZ) [x]) :: (map (\(MkPlays l ys) => MkPlays (FS l) (x::ys)) (playInits (S j) (S k) xs))

morphExtend : ((EFplaysType (S j) t1) -> t2) -> EFplaysType (S j) t1 -> EFplaysType (S j) t2
morphExtend {j = bnd} morph (MkPlays FZ {ok = ItIsFSucc} xs) impossible
morphExtend {j = bnd} morph (MkPlays (FS k) {ok = p}     xs) = MkPlays (FS k) {ok = p} (map morph (playInits (S bnd) (S (finToNat k)) xs))

coextPrf : Eq t1 => Eq t2 => (rel1 : Rel t1) -> (rel2 : Rel t2) -> (f : EFplaysType (S j) t1 -> t2) -> 
    IsGraphMorph morph (efRel rel1) rel2 -> (a : EFplaysType (S j) t1) -> (b : EFplaysType (S j) t1) -> 
    True = efRel rel1 (a, b) -> True = efRel rel2 (morphExtend f a, morphExtend f b)
coextPrf rel1 rel2 morph gmorphPrf (MkPlays FZ {ok = ItIsFSucc {k = FZ}} xs) pys relPrf impossible
coextPrf rel1 rel2 morph gmorphPrf xys (MkPlays FZ {ok = ItIsFSucc} ys) relPrf impossible
coextPrf rel1 rel2 morph (IsGraphMorphByElem gmorphPrf) (MkPlays (FS l1) xs) (MkPlays (FS l2) ys) relPrf = ?hole

coextensionEF : {sigma : Signature} -> {s1, s2 : Structure sigma} -> (bound : Nat) -> {auto ok : IsSucc bound} -> 
    StructMorph (EFComonadObj bound s1) s2 -> StructMorph (EFComonadObj bound s1) (EFComonadObj bound s2)
coextensionEF Z {ok = ItIsSucc} morph impossible
coextensionEF {sigma = Z} {s1 = (t1 ** vs1 ** interp1 ** eqt1)} {s2 = (t2 ** vs2 ** interp2 ** eqt2)} (S j) {ok = p} (Smor morph prof) = Smor (morphExtend morph) (EmptySigStructMorph Refl)
coextensionEF {sigma = S sig} {s1 = (t1 ** vs1 ** interp1 ** eqt1)} {s2 = (t2 ** vs2 ** interp2 ** eqt2)} (S j) {ok = p} (Smor morph (EmptySigStructMorph reflp)) = absurd (sym reflp)
coextensionEF {sigma = S sig} {s1 = (t1 ** vs1 ** interp1 ** eqt1)} {s2 = (t2 ** vs2 ** interp2 ** eqt2)} (S j) {ok = p} (Smor morph (ItIsStructMorph strutPrf)) = 
    Smor (morphExtend morph) (ItIsStructMorph prf)
            where   prf : (k : Fin (S sig)) -> IsGraphMorph (morphExtend morph) (efRel (interp1 k)) (efRel (interp2 k))
                    prf k = IsGraphMorphByElem (coextPrf {j = j} (interp1 k) (interp2 k) morph (strutPrf k)) 

EFIndexedComonadKleisli : {sigma : Signature} -> RIxCondComonadKleisli (Structure sigma) (StructCat sigma) Nat IsSucc
EFIndexedComonadKleisli = RIxCondComonadKleisliInfo EFComonadObj counitEF coextensionEF
