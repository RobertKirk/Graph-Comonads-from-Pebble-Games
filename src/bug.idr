module Test
import Data.Fin
import Data.So

%access public export
%default total

data IsSucc : (n : Nat) -> Type where
    ItIsSucc : IsSucc (S n)

Uninhabited (IsSucc Z) where
    uninhabited ItIsSucc impossible

Rel : Type -> Type
Rel t = (t,t) -> Bool

pebPlaysType : Nat -> Type -> Type
pebPlaysType pebs t = List (Fin pebs, t)

pebblesRelSuffix : Eq t => (as : pebPlaysType pebs t) -> (bs : pebPlaysType pebs t) -> Bool
pebblesRelSuffix xs ys with (isLTE (length xs) (length ys))
    | Yes prf = (isPrefixOf xs ys) && (isNothing (find ((==) (Basics.fst (last {ok = believe_me True} xs))) 
        (map fst (drop ((-) (length ys) (length xs)) ys))))
    | No contra = (isPrefixOf ys xs) && (isNothing (find ((==) (Basics.fst (last {ok = believe_me True} ys))) 
        (map fst (drop ((-) {smaller = believe_me True} (length xs) (length ys)) xs))))

pairMapRight : (t2 -> t3) -> (t1, t2) -> (t1, t3)
pairMapRight f (a, b) = (a, f b)

pebmap : (t1 -> t2) -> (pebPlaysType n t1) -> (pebPlaysType n t2)
pebmap vmap xs = map (pairMapRight vmap) xs

testing : Eq t1 => Eq t2 =>
    (pebs : Nat) -> {auto ok : IsSucc pebs} -> 
    (xs : pebPlaysType pebs t1) -> 
    (ys : pebPlaysType pebs t1) -> 
    (vmap : t1 -> t2) -> 
    (So (isPrefixOf xs ys)) -> 
    So (pebblesRelSuffix (pebmap vmap xs) (pebmap vmap ys))
testing Z {ok = p} xs ys vmap prf1 = ?zhole
testing (S n) {ok = p} xs ys vmap prf1 with (True) --can be anything here
    | True  = ?yhole
    | False = ?nohole