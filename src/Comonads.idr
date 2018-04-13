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
plays Z xs {ok = ItIsSucc} impossible
plays (S pebs) (Sing x) = concatNESofList (Singl (FZ,x))
    (iterate 
        (\ys => concat (map (\xs => (map (\p => (restrict pebs (toIntegerNat p), x):<:xs) [0..pebs])) ys)) 
        (map (\p => (Singl (restrict pebs (toIntegerNat p), x))) [0..pebs]))
plays (S pebs) (x:>:xs) = concatNESofNES (iterate (uplength (x:>:xs) pebs) (initial pebs (x:>:xs)))
            where   uplength : NEStream t -> (pebs:Nat) -> NEStream (playsType (S pebs) t) -> NEStream (playsType (S pebs) t)
                    uplength zs pebs ys = concatNESofNES (map 
                        (\els => concatNESofList 
                            (Singl (FZ, x)) 
                            (map (\el => map (\p => (restrict pebs (toIntegerNat p), el):<:els) [0..pebs]) zs)) 
                        ys)
                    initial : (pebs:Nat) -> NEStream t-> NEStream (playsType (S pebs) t)
                    initial pebs ys = concatNESofList (Singl (FZ,x)) (map (\y => map (\p => (Singl (restrict pebs (toIntegerNat p), y))) [0..pebs]) ys)

pebblesRelLT : Eq t =>  (xs : playsType n t) -> (ys : playsType n t) -> 
                        (ord : Ordering) -> ord = compare (length xs) (length ys) -> Bool
pebblesRelLT xs ys LT prf = (isPrefixOf xs ys) &&
        (isNothing (NonEmptyList.find ((==) (Basics.fst (last xs))) (map fst (drop (minus (length xs) (length ys)) ys))))
pebblesRelLT ys xs GT prf = (isPrefixOf xs ys) &&
        (isNothing (NonEmptyList.find ((==) (Basics.fst (last xs))) (map fst (drop (minus (length xs) (length ys)) ys))))
pebblesRelLT xs ys EQ prf = xs == ys

pebblesRel : Eq t => {pebs : Nat} -> {auto ok : IsSucc pebs} -> Rel t -> Rel (playsType n t)
pebblesRel r (xs, ys) = (pebblesRelLT xs ys (compare (length xs) (length ys)) Refl) && (r (snd (last xs), snd (last ys)))

TkObj : (pebs:Nat) -> {auto ok : IsSucc pebs} -> Graph -> Graph
TkObj Z g {ok = ItIsSucc } impossible
TkObj pebs (t ** vs ** e ** eqt) {ok = p} = 
    ((playsType pebs t) ** 
    (plays {ok = p} pebs vs) **
    (pebblesRel {n=pebs} e) **
    playsTypeEq)

pebmap : (t1 -> t2) -> (playsType n t1) -> (playsType n t2)
pebmap vmap xs = map (\(x,y) => (x, vmap y)) xs

TkMorph : {g1, g2 : Graph} -> (pebs:Nat) -> {auto ok : IsSucc pebs} -> Gmorph g1 g2 -> Gmorph (TkObj pebs g1) (TkObj pebs g2)
TkMorph Z morp {ok = ItIsSucc} impossible
TkMorph {g1 = (t1 ** v1 ** e1 **eq1)} {g2 = (t2 ** v2 ** e2 ** eq2)} pebs (Gmor vmap vmapIsGraphMorph) {ok = p} = 
    Gmor (pebmap vmap) (believe_me True)
  
pebbleFunctor : (pebs:Nat) -> {auto ok : IsSucc pebs} -> RFunctor Graph GraphCat
pebbleFunctor Z {ok = ItIsSucc} impossible
pebbleFunctor n {ok = p} = RFunctorInfo (TkObj n {ok = p}) (TkMorph n {ok = p})

counitPeb : {g : Graph} -> {n : Nat} -> {auto ok : IsSucc n} -> Gmorph (TkObj n g) g
counitPeb {n=Z} {ok = ItIsSucc} impossible
counitPeb {g = (t ** vs ** es ** eq)} {n = (S k)} {ok = p} = Gmor counitFunc (believe_me True)
    where   counitFunc : playsType m t -> t
            counitFunc ps = snd (last ps)

comultPeb : {g : Graph} -> {n : Nat} -> {auto ok : IsSucc n} -> Gmorph (TkObj n g) (TkObj n (TkObj n g))
comultPeb {n = Z} {ok = ItIsSucc} impossible
comultPeb {g = (t ** vs ** es ** eq)} {n = (S k)} {ok = p} = Gmor comultFunc (believe_me True)
    where   comultFunc : (playsType m t) -> (playsType m (playsType m t))
            comultFunc plays = zip (map fst plays) (inits plays)

pebbleIndexedComonad : RIxCondComonad Graph GraphCat Nat IsSucc
pebbleIndexedComonad = RIxCondComonadInfo pebbleFunctor counitPeb comultPeb
