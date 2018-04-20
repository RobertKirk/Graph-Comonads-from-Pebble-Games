module Comonads
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
playsType : Nat -> Type -> Type
playsType pebs t = NEList (Fin pebs, t)

[playsTypeEq] Interfaces.Eq t => Interfaces.Eq (playsType n t) where
    (==) (Singl x) (Singl y) = x == y
    (==) (x:<:xs) (y:<:ys) =
        if x==y then xs==ys else False
    (==) _ _ = False

-- the Non empty (infinite) stream of plays with pebs number of pebbles on the stream xs
plays : Eq t => (pebs:Nat) -> {auto ok : IsSucc pebs} -> (xs: NEStream t) -> (NEStream (playsType pebs t))
plays Z        xs {ok = ItIsSucc} impossible
plays (S pebs) xs = concatNESofNES (iterate (uplength xs pebs) (initial pebs xs))
            where   uplength : NEStream t -> (pebs:Nat) -> NEStream (playsType (S pebs) t) -> NEStream (playsType (S pebs) t)
                    uplength zs pebs ys = concatNESofNES (map 
                        (\els => concatNESofList 
                            (Singl (FZ, (head xs))) 
                            (map (\el => map (\p => (restrict pebs (toIntegerNat p), el):<:els) [0..pebs]) zs)) 
                        ys)
                    initial : (pebs:Nat) -> NEStream t-> NEStream (playsType (S pebs) t)
                    initial pebs ys = concatNESofList (Singl (FZ, (head xs))) (map (\y => 
                        map (\p => (Singl (restrict pebs (toIntegerNat p), y))) [0..pebs]) ys)

pebblesRelSuffix : Eq t => {pebs : Nat} -> {auto ok : IsSucc pebs} -> (as : playsType pebs t) -> (bs : playsType pebs t) -> Bool
pebblesRelSuffix xs ys with (compare (length xs) (length ys)) proof compprf
    | LT = (isPrefixOf xs ys) && (isNothing (NonEmptyList.find ((==) (Basics.fst (last xs))) 
        (map fst (drop ((-) 
        {smaller = ltImpliesLTE (length xs) (length ys) (compareToLT (length xs) (length ys) compprf)} 
        (length ys) (length xs)) ys))))
    | GT = (isPrefixOf ys xs) && (isNothing (NonEmptyList.find ((==) (Basics.fst (last ys))) 
        (map fst (drop ((-) 
        {smaller = ltImpliesLTE (length ys) (length xs) (compareToLT (length ys) (length xs) (compareSwap (length xs) (length ys) compprf))} 
        (length xs) (length ys)) xs))))
    | EQ = xs == ys

pebblesRel : Eq t => {pebs : Nat} -> {auto ok : IsSucc pebs} -> Rel t -> Rel (playsType pebs t)
pebblesRel r (xs, ys) = (pebblesRelSuffix xs ys) && (r (snd (last xs), snd (last ys)))

TkObj : (pebs:Nat) -> {auto ok : IsSucc pebs} -> Graph -> Graph
TkObj Z g {ok = ItIsSucc } impossible
TkObj pebs (t ** vs ** e ** eqt) {ok = p} = 
    ((playsType pebs t) ** 
    (plays {ok = p} pebs vs) **
    (pebblesRel {pebs=pebs} e) **
    playsTypeEq)

pairMapRight : (t2 -> t3) -> (t1,t2) -> (t1,t3)
pairMapRight f (a, b) = (a, f b)

pebmap : (t1 -> t2) -> (playsType n t1) -> (playsType n t2)
pebmap vmap xs = map (pairMapRight vmap) xs

pebmapPreservesLength : (f : t1 -> t2) -> (xs : playsType n t1) -> length (pebmap f xs) = length xs
pebmapPreservesLength f xs = mapPreservesLengthNel (pairMapRight f) xs

pebMapLastandVmapCommute : (xs : playsType pebs t1) -> (vmap : t1 -> t2) -> vmap (snd (last xs)) = snd (last (pebmap vmap xs))
pebMapLastandVmapCommute (Singl (p,x)) vmap = Refl
pebMapLastandVmapCommute (y:<:ys)      vmap = pebMapLastandVmapCommute ys vmap

TkMorphSndProof : Eq t1 => Eq t2 => (e1 : Rel t1) -> (e2 : Rel t2) -> (xs, ys : playsType pebs t1) -> 
    (vmap : t1 -> t2) -> IsGraphMorph vmap e1 e2 -> True = (e1 (snd (last xs), snd (last ys)))  -> 
    True = e2 (snd (last (pebmap vmap xs)), snd (last (pebmap vmap ys)))
TkMorphSndProof e1 e2 xs ys vmap (IsGraphMorphByElem vmapIsGraphMorph) e1relprf = 
    rewrite sym (pebMapLastandVmapCommute ys vmap) in 
    rewrite sym (pebMapLastandVmapCommute xs vmap) in 
    vmapIsGraphMorph (snd (last xs)) (snd (last ys)) e1relprf

TkMorphLTProof : Eq t1 => Eq t2 => (pebs : Nat) -> {auto ok : IsSucc pebs} ->  (xs, ys : playsType pebs t1) -> (vmap : t1 -> t2) ->
    LT = compare (length ys) (length xs) -> True = pebblesRelSuffix xs ys -> True = pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys)
TkMorphLTProof Z {ok = ItIsSucc} xs ys vmap ltproof prf1 impossible
TkMorphLTProof (S k)    {ok = p} xs ys vmap ltproof prf1 = ?ltproofhole

TkMorphGTProof : Eq t1 => Eq t2 => (pebs : Nat) -> {auto ok : IsSucc pebs} ->  (xs, ys : playsType pebs t1) -> (vmap : t1 -> t2) ->
    GT = compare (length ys) (length xs) -> True = pebblesRelSuffix xs ys -> True = pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys)
TkMorphGTProof Z {ok = ItIsSucc} xs ys vmap ltproof prf1 impossible
TkMorphGTProof (S k)    {ok = p} xs ys vmap ltproof prf1 = ?gtproofhole

eqProofInt : Eq t1 => (pebs : Nat) -> {auto ok : IsSucc pebs} -> (xs, ys : playsType pebs t1) -> True = pebblesRelSuffix xs ys -> 
    EQ = compare (length xs) (length ys) -> True = xs == ys
eqProofInt Z {ok = ItIsSucc} xs ys p1 p2 impossible
eqProofInt (S k) {ok =p} xs ys suffixPrf eqPrf = ?hole45 --rewrite sym eqPrf in suffixPrf

TkMorphEQProof : Eq t1 => Eq t2 => (pebs : Nat) -> {auto ok : IsSucc pebs} ->  (xs, ys : playsType pebs t1) -> (vmap : t1 -> t2) ->
    EQ = compare (length ys) (length xs) -> True = pebblesRelSuffix xs ys -> True = pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys)
TkMorphEQProof Z {ok = ItIsSucc} xs ys vmap ltproof prf1 impossible
TkMorphEQProof (S k)    {ok = p} xs ys vmap ltproof prf1 = ?holeymoley
    -- rewrite pebmapPreservesLength vmap xs in 
    -- rewrite pebmapPreservesLength vmap ys in 
    -- rewrite sym (eqReflexiveCompare (length ys) (length xs) ltproof) in prf1                    

TkMorphProof : Eq t1 => Eq t2 => (pebs : Nat) -> {auto ok : IsSucc pebs} -> (e1 : Rel t1) -> (e2 : Rel t2) -> 
    (vmap : t1 -> t2) -> (IsGraphMorph vmap e1 e2) -> (a : playsType pebs t1) -> (b : playsType pebs t1) -> 
    True = (pebblesRel {pebs = pebs} e1) (a, b) -> True = (pebblesRel {pebs = pebs} e2) (pebmap vmap a, pebmap vmap b)
TkMorphProof Z {ok = ItIsSuc} e1 e2 vmap prf a b prf2 impossible
TkMorphProof (S k) {ok = p} e1 e2 vmap (IsGraphMorphByElem vmapIsGraphMorph) xs ys e1relprf with (compare (length ys) (length xs)) proof compPrf
        | LT = 
            andCombines (pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys))
                        (e2 (snd (last (pebmap vmap xs)), snd (last (pebmap vmap ys))))
                        (TkMorphLTProof (S k) {ok = p} xs ys vmap compPrf (andTrueImpliesConjunctsTrueL e1relprf))
                        (TkMorphSndProof e1 e2 xs ys vmap (IsGraphMorphByElem vmapIsGraphMorph) (andTrueImpliesConjunctsTrueR e1relprf))
        | GT = 
            andCombines (pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys))
                        (e2 (snd (last (pebmap vmap xs)), snd (last (pebmap vmap ys))))
                        (TkMorphGTProof (S k) {ok = p} xs ys vmap compPrf (andTrueImpliesConjunctsTrueL e1relprf))
                        (TkMorphSndProof e1 e2 xs ys vmap (IsGraphMorphByElem vmapIsGraphMorph) (andTrueImpliesConjunctsTrueR e1relprf))
        | EQ = 
            andCombines (pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys))
                        (e2 (snd (last (pebmap vmap xs)), snd (last (pebmap vmap ys))))
                        (TkMorphEQProof (S k) {ok = p} xs ys vmap compPrf (andTrueImpliesConjunctsTrueL e1relprf))
                        (TkMorphSndProof e1 e2 xs ys vmap (IsGraphMorphByElem vmapIsGraphMorph) (andTrueImpliesConjunctsTrueR e1relprf))

TkMorph : {g1, g2 : Graph} -> (pebs : Nat) -> {auto ok : IsSucc pebs} -> Gmorph g1 g2 -> Gmorph (TkObj pebs g1) (TkObj pebs g2)
TkMorph Z morp {ok = ItIsSucc} impossible
TkMorph {g1 = (t1 ** v1 ** e1 ** eq1)} {g2 = (t2 ** v2 ** e2 ** eq2)} pebs (Gmor vmap (IsGraphMorphByElem vmapIsGraphMorph)) {ok = p} = 
    Gmor (pebmap vmap) (IsGraphMorphByElem prf)
        where   prf : (a : playsType pebs t1) -> (b : playsType pebs t1) -> True = (pebblesRel e1) (a, b) -> 
                    True = (pebblesRel e2) (pebmap vmap a, pebmap vmap b)
                prf xs ys prfae1b = 
                    (TkMorphProof pebs {ok = p} e1 e2 vmap (IsGraphMorphByElem vmapIsGraphMorph) xs ys prfae1b)
  
pebbleFunctor : (pebs:Nat) -> {auto ok : IsSucc pebs} -> RFunctor Graph GraphCat
pebbleFunctor Z {ok = ItIsSucc} impossible
pebbleFunctor n {ok = p} = RFunctorInfo (TkObj n {ok = p}) (TkMorph n {ok = p})

counitPeb : {g : Graph} -> {n : Nat} -> {auto ok : IsSucc n} -> Gmorph (TkObj n g) g
counitPeb {n = Z} {ok = ItIsSucc} impossible
counitPeb {g = (t ** vs ** es ** eq)} {n = (S k)} {ok = p} = Gmor counitFunc (IsGraphMorphByElem prf)
    where   counitFunc : playsType m t -> t
            counitFunc ps = snd (last ps)
            prf : (a : playsType (S k) t) -> (b : playsType (S k) t) -> True = (pebblesRel {pebs = (S k)} es) (a,b) -> 
                True = es (counitFunc a, counitFunc b)
            prf xs ys prfaesb = andTrueImpliesConjunctsTrueR prfaesb

-- comultPebProof : (a : playsType (S k) t) -> (b : playsType (S k) t) -> True = (pebblesRel {pebs = (S k)} es) (a,b) -> 
--     True = (pebblesRel {pebs = (S k)} (pebblesRel {pebs = (S k)} es)) (comultFunc a, comultFunc b)

comultPeb : {g : Graph} -> {n : Nat} -> {auto ok : IsSucc n} -> Gmorph (TkObj n g) (TkObj n (TkObj n g))
comultPeb {n = Z} {ok = ItIsSucc} impossible
comultPeb {g = (t ** vs ** es ** eq)} {n = (S k)} {ok = p} = Gmor comultFunc (IsGraphMorphByElem prf)
    where   comultFunc : (playsType m t) -> (playsType m (playsType m t))
            comultFunc plays = zip (map fst plays) (inits plays)
            prf = ?holecomult
            -- prf : (a : playsType (S k) t) -> (b : playsType (S k) t) -> True = (pebblesRel {pebs = (S k)} es) (a,b) -> 
            --     True = (pebblesRel {pebs = (S k)} (pebblesRel {pebs = (S k)} es)) (comultFunc a, comultFunc b)
            -- prf xs ys prfaesb = ?hole2

pebbleIndexedComonad : RIxCondComonad Graph GraphCat Nat IsSucc
pebbleIndexedComonad = RIxCondComonadInfo pebbleFunctor counitPeb comultPeb
