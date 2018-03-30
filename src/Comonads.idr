module Comonads
import Data.Fin
import src.ProofHelpers

import src.RCategories
import src.Graphs

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

finUnit : Fin (S n)
finUnit = 0

-- the list of plays of length up to n with pebs number of pebbles on the list xs
playsN : Eq t => (n:Nat) -> (pebs:Nat) -> (xs: List t) -> (List (playsType pebs t))
playsN Z pebs xs = [[]]
playsN n pebs [] = [[]]
playsN n Z xs = [[]]
playsN (S n) (S pebs) (x::xs) = let plays = playsN n (S pebs) (x::xs) in
    plays ++ [play ++ [(restrict pebs (toIntegerNat peb),el)] 
                | play <- plays, el <- (x::xs), peb <- [0..(S pebs)]]

pebblesRel : Eq t => {n: Nat} -> (xs: List t) -> Rel t -> Rel (playsType n t)
pebblesRel xs r ([],_) = True
pebblesRel xs r (_,[]) = True
pebblesRel xs r ((p1::ps1),(p2::ps2)) = 
    ((List.isPrefixOf (p1::ps1) (p2::ps2)) &&
        (isNothing (find (\x => True) 
                    (List.take (minus (length (p2::ps2)) (length (p1::ps1))) (reverse (map Basics.fst (p2::ps2)))))))
    || ((List.isPrefixOf (p2::ps2) (p1::ps1)) && 
        (isNothing (find ((==) (Basics.fst (last (p2::ps2)))) 
                (List.take (minus (length (p1::ps1)) (length (p2::ps2))) (reverse (map Basics.fst (p1::ps1)))))))
    && r (snd (last (p1::ps1)), snd (last (p2::ps2)))
    

TkObj : Nat -> Graph -> Graph
TkObj pebs (t ** vs ** e ** eqt) = 
    ((playsType pebs t) ** 
    (playsN (length vs) pebs vs) ** -- length vs should really be infinite here
    (pebblesRel {n=pebs} vs e) **
    playsTypeEq)
  
-- myMorph : length v1 = length v2 -> playsType pebs v1 -> playsType pebs v2
-- myMorph pf xs = rewrite sym pf in map id xs

pebmap : (t1 -> t2) -> (playsType n t1) -> (playsType n t2)
pebmap vmap xs = map (\(x,y) => (x, vmap y)) xs

TkMorph : {g1, g2 : Graph} -> (pebs:Nat) -> Gmorph g1 g2 -> Gmorph (TkObj pebs g1) (TkObj pebs g2)
TkMorph {g1 = (t1 ** v1 ** e1 **eq1)} {g2 = (t2 ** v2 ** e2 ** eq2)} pebs (Gmor vmap vmapIsMappedList vmapIsGraphMorph) = 
    Gmor (pebmap vmap) (believe_me True) (believe_me True)
  
pebbleFunctor : Nat -> RFunctor Graph GraphCat 
pebbleFunctor n = RFunctorInfo (TkObj n) (TkMorph n)

counitFunc : playsType k t -> t
counitFunc [] = ?hole
counitFunc (p::ps) = snd (last (p::ps))

counitPeb : {g : Graph} -> {n : Nat} -> Gmorph (TkObj n g) g
counitPeb {g = (t ** vs ** es ** eq)} = Gmor counitFunc (believe_me True) (believe_me True)
 
comultFunc : (playsType k t) -> (playsType k (playsType k t))
comultFunc plays = zip (map fst plays) (inits plays)

comultPeb : {g : Graph} -> {n : Nat} -> Gmorph (TkObj n g) (TkObj n (TkObj n g))
comultPeb {g = (t ** vs ** es ** eq)} = Gmor comultFunc (believe_me True) (believe_me True)

pebbleIndexedComonad : RIxComonad Graph GraphCat Nat
pebbleIndexedComonad = RIxComonadInfo pebbleFunctor counitPeb comultPeb
