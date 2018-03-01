module Comonads
import Data.Fin
import src.Categories
import src.Graphs

-- a play with n pebbles is a list of pairs of the pebble being played each turn, 
-- and the position in the list of the element the pebble is played on. 
-- note the pebble start indexed at 0, so we can use (Fin pebs) here.
playsType : Nat -> (List t) -> Type
playsType pebs xs = List ((Fin pebs), (Fin (length xs)))

finUnit : Fin (S n)
finUnit = 0

-- the list of plays of length up to N with pebs pebbles on the list xs
playsN : Nat -> (pebs:Nat) -> (xs: List t) -> (List (playsType pebs xs))
playsN Z pebs xs = [[]]
playsN n pebs [] = [[]]
playsN n Z xs = [[]]
playsN (S n) (S pebs) (x::xs) = let plays = playsN n (S pebs) (x::xs) in
    plays ++ [play ++ [((restrict pebs (toIntegerNat peb)), (restrict (length xs) (toIntegerNat el)))] 
                | play <- plays, el <- [0..(length (x::xs))], peb <-[0..(S pebs)]]

pebblesRel : {n: Nat} -> (xs: List t) -> Rel t -> Rel (playsType n xs)
pebblesRel xs r = (\((p1::ps1),(p2::ps2)) => 
    (((List.isPrefixOf (p1::ps1) (p2::ps2)) && 
        (isNothing (find ((==) (Basics.fst (last (p1::ps1)))) 
                    (List.take (minus (length (p2::ps2)) (length (p1::ps1))) (reverse (map Basics.fst (p2::ps2)))))))
    || ((List.isPrefixOf (p2::ps2) (p1::ps1)) && 
        (isNothing (find ((==) (Basics.fst (last (p2::ps2)))) 
                (List.take (minus (length (p1::ps1)) (length (p2::ps2))) (reverse (map Basics.fst (p1::ps1))))))))
    && (r (List.index (finToNat (Basics.snd (last (p1::ps1)))) xs, List.index (finToNat (Basics.snd (last (p2::ps2)))) xs))
    )

-- TkObj : Nat -> Graph -> Graph
-- TkObj pebs (t ** vs ** e) = 
--     ((playsType pebs v) ** 
--     (playsN (length v) pebs vs) **
--     pebblesRel pebs vs e
--     )

-- TkMorph : Nat -> Gmorph g1 g2 -> Gmorph (TkObj g1) (TkObj g2)
-- TkMorph n (Gmor vmap emap) = Gmor (map (\(p,el) => (p, vmap el))) (\(v1,v2) => )