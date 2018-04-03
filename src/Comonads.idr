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
playsType pebs t = List ((Fin pebs), t)

[playsTypeEq] Interfaces.Eq t => Interfaces.Eq (playsType n t) where
    (==) [] [] = True
    (==) (x::xs) (y::ys) =
        if x==y then xs==ys else False
    (==) _ _ = False

-- the Non empty (infinite) stream of plays with pebs number of pebbles on the stream xs
plays : Eq t => (pebs:Nat) -> {auto ok : IsSucc pebs}-> (xs: NEStream t) -> (NEStream (playsType pebs t))
plays Z xs {ok = ItIsSucc} impossible
plays (S pebs) (Sing x) = concatNESofList [(FZ,x)]
    (iterate (\ys => concat (map (\xs => (map (\p => (restrict pebs (toIntegerNat p), x)::xs) [0..pebs])) ys)) (map (\p => [(restrict pebs (toIntegerNat p), x)]) [0..pebs]))
plays (S pebs) (x:>:xs) = concatNESofNES(iterate (uplength (x:>:xs) pebs) (initial pebs (x:>:xs)))
            where   uplength : NEStream t -> (pebs:Nat) -> NEStream (playsType (S pebs) t) -> NEStream (playsType (S pebs) t)
                    uplength xs pebs ys = concatNESofNES (map (\zs =>
                        concatNESofList [(FZ,x)] (map (\z => map (\p => (restrict pebs (toIntegerNat p), z)::zs) [0..pebs]) xs)) 
                        ys)
                    initial : (pebs:Nat) -> NEStream t-> NEStream (playsType (S pebs) t)
                    initial pebs xs = concatNESofList [(FZ,x)] (map (\y => map (\p => [(restrict pebs (toIntegerNat p), y)]) [0..pebs]) xs)

pebblesRel : Eq t => {n: Nat} -> Rel t -> Rel (playsType n t)
pebblesRel r ([],_) = True
pebblesRel r (_,[]) = True
pebblesRel r ((p1::ps1),(p2::ps2)) = 
    (((List.isPrefixOf (p1::ps1) (p2::ps2)) &&
        (isNothing (find ((==) (Basics.fst (last (p1::ps1))))
                    (List.take (minus (length (p2::ps2)) (length (p1::ps1))) (reverse (map Basics.fst (p2::ps2)))))))
    || ((List.isPrefixOf (p2::ps2) (p1::ps1)) && 
        (isNothing (find ((==) (Basics.fst (last (p2::ps2)))) 
                (List.take (minus (length (p1::ps1)) (length (p2::ps2))) (reverse (map Basics.fst (p1::ps1))))))))
    && r (snd (last (p1::ps1)), snd (last (p2::ps2)))
    

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

-- counitFunc : playsType k t -> t
-- counitFunc [] = ?hole
-- counitFunc (p::ps) = snd (last (p::ps))

counitPeb : {g : Graph} -> {n : Nat} -> {auto ok : IsSucc n} -> Gmorph (TkObj n g) g
counitPeb {n=Z} {ok = ItIsSucc} impossible
counitPeb {g = (t ** vs ** es ** eq)} {n = (S k)} {ok = p} = Gmor (assert_total counitFunc) (believe_me True)
    where counitFunc : playsType m t -> t
          counitFunc [] = head vs -- This isn't correct, but we'll never use counitFunc on non-empty lists
          counitFunc (p::ps) = snd (last (p::ps))
 
comultFunc : (playsType k t) -> (playsType k (playsType k t))
comultFunc plays = zip (map fst plays) (inits plays)

comultPeb : {g : Graph} -> {n : Nat} -> {auto ok : IsSucc n} -> Gmorph (TkObj n g) (TkObj n (TkObj n g))
comultPeb {n = Z} {ok = ItIsSucc} impossible
comultPeb {g = (t ** vs ** es ** eq)} {n = (S k)} {ok = p} = Gmor comultFunc (believe_me True)

pebbleIndexedComonad : RIxCondComonad Graph GraphCat Nat IsSucc
pebbleIndexedComonad = RIxCondComonadInfo pebbleFunctor counitPeb comultPeb
