module Comonads
import Data.Fin
import src.Categories
import src.Graphs
import src.ProofHelpers

%default total

-- a play with n pebbles is a list of pairs of the pebble being played each turn, 
-- and the position in the list of the element the pebble is played on. 
-- note the pebble start indexed at 0, so we can use (Fin pebs) here.
playsType : Nat -> (List t) -> Type
playsType pebs xs = List ((Fin pebs), (Fin (length xs)))

finUnit : Fin (S n)
finUnit = 0

-- the list of plays of length up to N with pebs pebbles on the list xs
total playsN : (n:Nat) -> (pebs:Nat) -> (xs: List t) -> (List (playsType pebs xs))
playsN Z pebs xs = [[]]
playsN n pebs [] = [[]]
playsN n Z xs = [[]]
playsN (S n) (S pebs) (x::xs) = let plays = playsN n (S pebs) (x::xs) in
    plays ++ [play ++ [((restrict pebs (toIntegerNat peb)), (restrict (length xs) (toIntegerNat el)))] 
                | play <- plays, el <- [0..(length (x::xs))], peb <-[0..(S pebs)]]

pebblesRel : {n: Nat} -> (xs: List t) -> Rel t -> Rel (playsType n xs)
pebblesRel xs r ([],_) = True
pebblesRel xs r (_,[]) = True
pebblesRel xs r ((p1::ps1),(p2::ps2)) = 
    (((List.isPrefixOf (p1::ps1) (p2::ps2)) && 
        (isNothing (find ((==) (Basics.fst (last (p1::ps1)))) 
                    (List.take (minus (length (p2::ps2)) (length (p1::ps1))) (reverse (map Basics.fst (p2::ps2)))))))
    || ((List.isPrefixOf (p2::ps2) (p1::ps1)) && 
        (isNothing (find ((==) (Basics.fst (last (p2::ps2)))) 
                (List.take (minus (length (p1::ps1)) (length (p2::ps2))) (reverse (map Basics.fst (p1::ps1))))))))
    && (r (List.index {ok = believe_me True} (finToNat (Basics.snd (last (p1::ps1)))) xs, List.index {ok = believe_me True} (finToNat (Basics.snd (last (p2::ps2)))) xs))
    

TkObj : Nat -> Graph -> Graph
TkObj pebs (MkG (t ** vs ** e)) = 
    MkG ((playsType pebs vs) ** 
    (playsN (length vs) pebs vs) ** -- length vs should really be infinite here
    pebblesRel {n=pebs} vs e
    )

myMorph : length v1 = length v2 -> playsType pebs v1 -> playsType pebs v2
myMorph pf xs = rewrite sym pf in map id xs

TkMorph : {g1,g2 : Graph} -> (pebs:Nat) -> Gmorph g1 g2 -> Gmorph (TkObj pebs g1) (TkObj pebs g2)
TkMorph {g1 = MkG (t1 ** v1 ** e1)} {g2 = MkG (t2 ** v2 ** e2)} pebs (Gmor vmap vmapIsMappedList vmapIsGraphMorph) = 
    Gmor (rewrite (mappedListsHaveSameLength vmap v1 v2 vmapIsMappedList) in map id) ?hole2 ?hole3
    
-- Categories.Functor Gmorph (TkObj Z) where
--     fmap = (TkMorph Z)
