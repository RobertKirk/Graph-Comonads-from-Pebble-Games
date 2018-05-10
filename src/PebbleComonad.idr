module PebbleComonad
import Data.Fin
import src.ProofHelpers
import src.NonEmptyStream
import src.NonEmptyList

import src.RCategories
import src.Graphs

%hide Stream.(::)
%access public export
%default total

-- a play with n pebbles is a list of pairs of the pebble being played each turn, 
-- and the position in the list of the element the pebble is played on. 
-- note the pebble start indexed at 0, so we can use (Fin pebs) here.
pebPlaysType : Nat -> Type -> Type
pebPlaysType pebs t = NEList (Fin pebs, t)

[pebPlaysTypeEq] Interfaces.Eq t => Interfaces.Eq (pebPlaysType n t) where
    (==) (Singl x) (Singl y) = x == y
    (==) (x:<:xs) (y:<:ys) =
        if x==y then xs==ys else False
    (==) _ _ = False

-- the Non empty (infinite) stream of plays with pebs number of pebbles on the stream xs
pebPlays : Eq t => (pebs : Nat) -> {auto ok : IsSucc pebs} -> (xs: NEStream t) -> (NEStream (pebPlaysType pebs t))
pebPlays Z        xs {ok = ItIsSucc} impossible
pebPlays (S pebs) xs = concatNESofNES (iterate (uplength xs pebs) (initial pebs xs))
            where   uplength : NEStream t -> (pebs:Nat) -> NEStream (pebPlaysType (S pebs) t) -> NEStream (pebPlaysType (S pebs) t)
                    uplength zs pebs ys = concatNESofNES (map 
                        (\els => concatNESofList 
                            (Singl (FZ, (head xs))) 
                            (map (\el => map (\p => (restrict pebs (toIntegerNat p), el):<:els) [0..pebs]) zs)) 
                        ys)
                    initial : (pebs:Nat) -> NEStream t-> NEStream (pebPlaysType (S pebs) t)
                    initial pebs ys = concatNESofList (Singl (FZ, (head xs))) (map (\y => 
                        map (\p => (Singl (restrict pebs (toIntegerNat p), y))) [0..pebs]) ys)

pebblesRelSuffix : Eq t => (as : pebPlaysType pebs t) -> (bs : pebPlaysType pebs t) -> Bool
pebblesRelSuffix xs ys with (isLTE (length xs) (length ys))
    | Yes prf = (NonEmptyList.isPrefixOf xs ys) && (isNothing (NonEmptyList.find ((==) (Basics.fst (last xs))) 
        (map fst (drop ((-) (length ys) (length xs)) ys))))
    | No contra = (isPrefixOf ys xs) && (isNothing (NonEmptyList.find ((==) (Basics.fst (last ys))) 
        (map fst (drop ((-) {smaller = notLTEImpliesLT _ _ contra} (length xs) (length ys)) xs))))

pebblesRel : Eq t => Rel t -> Rel (pebPlaysType pebs t)
pebblesRel r (xs, ys) = (pebblesRelSuffix xs ys) && (r (snd (last xs), snd (last ys)))

PebComonadObj : (pebs:Nat) -> {auto ok : IsSucc pebs} -> Graph -> Graph
PebComonadObj Z g {ok = ItIsSucc } impossible
PebComonadObj pebs (t ** vs ** e ** eqt) {ok = p} = 
    ((pebPlaysType pebs t) ** 
    (pebPlays {ok = p} pebs vs) **
    (pebblesRel e) **
    pebPlaysTypeEq)

pairMapRight : (t2 -> t3) -> (t1, t2) -> (t1, t3)
pairMapRight f (a, b) = (a, f b)

pebmap : (t1 -> t2) -> (pebPlaysType n t1) -> (pebPlaysType n t2)
pebmap vmap xs = map (pairMapRight vmap) xs

pebmapPreservesLength : (f : t1 -> t2) -> (xs : pebPlaysType n t1) -> length (pebmap f xs) = length xs
pebmapPreservesLength f xs = mapPreservesLengthNel (pairMapRight f) xs

pebMapLastandVmapCommute : (xs : pebPlaysType pebs t1) -> (vmap : t1 -> t2) -> vmap (snd (last xs)) = snd (last (pebmap vmap xs))
pebMapLastandVmapCommute (Singl (p,x)) vmap = Refl
pebMapLastandVmapCommute (y:<:ys)      vmap = pebMapLastandVmapCommute ys vmap

PebComonadMorphSndProof : Eq t1 => Eq t2 => (e1 : Rel t1) -> (e2 : Rel t2) -> (xs, ys : pebPlaysType pebs t1) -> 
    (vmap : t1 -> t2) -> IsGraphMorph vmap e1 e2 -> True = (e1 (snd (last xs), snd (last ys)))  -> 
    True = e2 (snd (last (pebmap vmap xs)), snd (last (pebmap vmap ys)))
PebComonadMorphSndProof e1 e2 xs ys vmap (IsGraphMorphByElem vmapIsGraphMorph) e1relprf = 
    rewrite sym (pebMapLastandVmapCommute ys vmap) in 
    rewrite sym (pebMapLastandVmapCommute xs vmap) in 
    vmapIsGraphMorph (snd (last xs)) (snd (last ys)) e1relprf

PebComonadMorphLTEProof : Eq t1 => Eq t2 => (pebs : Nat) -> {auto ok : IsSucc pebs} ->  (xs : pebPlaysType pebs t1) -> (ys : pebPlaysType pebs t1) -> 
    (vmap : t1 -> t2) -> LTE (length xs) (length ys) -> 
    True = (isPrefixOf xs ys) && (isNothing (NonEmptyList.find ((==) (Basics.fst (last xs))) 
    (map Basics.fst (drop ((-) (length ys) (length xs)) ys)))) -> 
    True = pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys)
PebComonadMorphLTEProof Z {ok = ItIsSucc} xs ys vmap ltproof prf1 impossible
PebComonadMorphLTEProof (S j) {ok = p} xs ys vmap ltproof prf1 = ?pebMorphLTEHole -- with (isLTE (length (pebmap vmap xs)) (length (pebmap vmap ys)))
    -- | Yes yproof = ?yhole
    -- | No cadgadgontra = ?ltnadgadghole

PebComonadMorphGTProof : Eq t1 => Eq t2 => (pebs : Nat) -> {auto ok : IsSucc pebs} ->  (xs, ys : pebPlaysType pebs t1) -> (vmap : t1 -> t2) ->
    LTE (length ys) (length xs) -> 
    (True = (NonEmptyList.isPrefixOf ys xs) && (isNothing (NonEmptyList.find ((==) (Basics.fst (last ys))) 
    (map Basics.fst (drop ((-) (NonEmptyList.length xs) (NonEmptyList.length ys)) xs))))) -> 
    True = pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys)
PebComonadMorphGTProof Z {ok = ItIsSucc} xs ys vmap ltproof prf1 impossible
PebComonadMorphGTProof (S k) {ok = p} xs ys vmap ltproof prf1 = ?pebMorphGTHole -- with (isLTE (NonEmptyList.length (pebmap vmap ys)) (NonEmptyList.length (pebmap vmap xs)))
    -- | Yes yproof = ?yhole
    -- | No cadgadgontra = ?ltnadgadghole

PebComonadMorphProof : Eq t1 => Eq t2 => (pebs : Nat) -> {auto ok : IsSucc pebs} -> (e1 : Rel t1) -> (e2 : Rel t2) -> 
    (vmap : t1 -> t2) -> (IsGraphMorph vmap e1 e2) -> (a : pebPlaysType pebs t1) -> (b : pebPlaysType pebs t1) -> 
    True = (pebblesRel {pebs = pebs} e1) (a, b) -> True = (pebblesRel {pebs = pebs} e2) (pebmap vmap a, pebmap vmap b)
PebComonadMorphProof Z {ok = ItIsSuc} e1 e2 vmap prf a b prf2 impossible
PebComonadMorphProof (S k) {ok = p} e1 e2 vmap (IsGraphMorphByElem vmapIsGraphMorph) xs ys e1relprf with (isLTE (length xs) (length ys))
        | Yes yprf =
            andCombines (pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys))
                        (e2 (snd (last (pebmap vmap xs)), snd (last (pebmap vmap ys))))
                        (PebComonadMorphLTEProof (S k) xs ys vmap yprf (conjunctsTrueL e1relprf))
                        (PebComonadMorphSndProof e1 e2 xs ys vmap (IsGraphMorphByElem vmapIsGraphMorph) (conjunctsTrueR e1relprf))
        | No contra =
            andCombines (pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys))
                        (e2 (snd (last (pebmap vmap xs)), snd (last (pebmap vmap ys))))
                        (PebComonadMorphGTProof (S k) xs ys vmap (notLTEImpliesLT _ _ contra) (conjunctsTrueL e1relprf))
                        (PebComonadMorphSndProof e1 e2 xs ys vmap (IsGraphMorphByElem vmapIsGraphMorph) (conjunctsTrueR e1relprf))

PebComonadMorph : {g1, g2 : Graph} -> (pebs : Nat) -> {auto ok : IsSucc pebs} -> Gmorph g1 g2 -> Gmorph (PebComonadObj pebs g1) (PebComonadObj pebs g2)
PebComonadMorph Z morp {ok = ItIsSucc} impossible
PebComonadMorph {g1 = (t1 ** v1 ** e1 ** eq1)} {g2 = (t2 ** v2 ** e2 ** eq2)} pebs (Gmor vmap (IsGraphMorphByElem vmapIsGraphMorph)) {ok = p} = 
    Gmor (pebmap vmap) (IsGraphMorphByElem prf)
        where   prf : (a : pebPlaysType pebs t1) -> (b : pebPlaysType pebs t1) -> True = (pebblesRel e1) (a, b) -> 
                    True = (pebblesRel e2) (pebmap vmap a, pebmap vmap b)
                prf = PebComonadMorphProof pebs {ok = p} e1 e2 vmap (IsGraphMorphByElem vmapIsGraphMorph)
  
pebbleFunctor : (pebs:Nat) -> {auto ok : IsSucc pebs} -> RFunctor Graph GraphCat
pebbleFunctor Z {ok = ItIsSucc} impossible
pebbleFunctor n {ok = p} = RFunctorInfo (PebComonadObj n {ok = p}) (PebComonadMorph n {ok = p})

counitPeb : {g : Graph} -> (n: Nat) -> {auto ok : IsSucc n} -> Gmorph (PebComonadObj n g) g
counitPeb {n = Z} {ok = ItIsSucc} impossible
counitPeb {g = (t ** vs ** es ** eq)} {n = (S k)} {ok = p} = Gmor counitFunc (IsGraphMorphByElem prf)
    where   counitFunc : pebPlaysType m t -> t
            counitFunc ps = snd (last ps)
            prf : (a : pebPlaysType (S k) t) -> (b : pebPlaysType (S k) t) -> True = (pebblesRel {pebs = (S k)} es) (a,b) -> 
                True = es (counitFunc a, counitFunc b)
            prf xs ys prfaesb = conjunctsTrueR prfaesb

comultFunc : (pebPlaysType m t) -> (pebPlaysType m (pebPlaysType m t))
comultFunc plays = zip (map fst plays) (inits plays)    
            
-- comultPebProof : Eq t => (k : Nat) -> (es : Rel t) -> (a : pebPlaysType (S k) t) -> (b : pebPlaysType (S k) t) -> 
--     True = (pebblesRel @{pebPlaysTypeEq} es) (a,b) -> 
--     True = (pebblesRel {t = pebPlaysType (S k) t} (pebblesRel {t = t} @{pebPlaysTypeEq} es)) 
--         (comultFunc a, comultFunc b)
-- comultPebProof = ?holecomilt

comultPeb : {g : Graph} -> (n: Nat) -> {auto ok : IsSucc n} -> Gmorph (PebComonadObj n g) (PebComonadObj n (PebComonadObj n g))
comultPeb {n = Z} {ok = ItIsSucc} impossible
comultPeb {g = (t ** vs ** es ** eq)} {n = (S k)} {ok = p} = Gmor comultFunc (IsGraphMorphByElem prf)
    where   prf = ?pebComultMorphProof
            -- prf : (a : pebPlaysType (S k) t) -> (b : pebPlaysType (S k) t) -> True = (pebblesRel {pebs = (S k)} es) (a,b) -> 
            --     True = (pebblesRel {pebs = (S k)} (pebblesRel {pebs = (S k)} es)) (comultFunc a, comultFunc b)
            -- prf xs ys prfaesb = ?hole2

pebbleIndexedComonad : RIxCondComonad Graph GraphCat Nat IsSucc
pebbleIndexedComonad = RIxCondComonadInfo pebbleFunctor counitPeb comultPeb

pebmorphExtend : (pebs : Nat) -> {auto ok : IsSucc pebs} -> ((pebPlaysType pebs t1) -> t2) -> pebPlaysType pebs t1 -> pebPlaysType pebs t2
pebmorphExtend Z {ok = IsSucc} f plays impossible
pebmorphExtend (S k) morph plays = zip (map fst plays) (map morph (inits plays))

coextensionPeb : {g1, g2 : Graph} -> (n : Nat) -> {auto ok : IsSucc n} -> Gmorph (PebComonadObj n g1) g2 -> 
    Gmorph (PebComonadObj n g1) (PebComonadObj n g2)
coextensionPeb Z {ok = ItIsSucc} morph impossible
coextensionPeb {g1 = (t1 ** v1 ** e1 ** eq1)} {g2 = (t2 ** v2 ** e2 ** eq2)} (S k) {ok = p} (Gmor morph prf) = 
    Gmor (pebmorphExtend (S k) {ok = p} morph) prof 
        where prof = ?pebCoextPrf

pebbleIndexedComonadKleisli : RIxCondComonadKleisli Graph GraphCat Nat IsSucc
pebbleIndexedComonadKleisli = RIxCondComonadKleisliInfo PebComonadObj counitPeb coextensionPeb
