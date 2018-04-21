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

data EFplaysType : (n: Nat) -> (t : Type) -> Type where
    MkPlay : (k : Fin n) -> Vect (finToNat k) t -> EFplaysType n t

[EFplaysTypeEq] Eq t => Eq (EFplaysType n t) where
    (==) (EFplay k xs) (EFplay j ys) = k == j && toList xs == toList ys

EFplays : Eq t => (bound : Nat) -> {auto ok = IsSucc bound} -> (xs : NEStream t) -> NEStream (EFplaysType bound t)
EFplays Z {ok = ItIsSucc} xs impossible
EFplays (S k) {ok = p}    xs = concatNESofNES (iterate )