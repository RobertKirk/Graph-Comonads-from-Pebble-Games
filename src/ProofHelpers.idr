module ProofHelpers
import Data.Fin

import src.NonEmptyList
import src.NonEmptyStream

%access public export
%default total

mappedListsHaveSameLength : (f : t1 -> t2) -> (xs : List t1) -> (ys : List t2) -> map f xs = ys -> length xs = length ys
mappedListsHaveSameLength f xs ys pf = rewrite sym pf in rewrite mapPreservesLength f xs in Refl

intermediateMapsCompose : (f : t1 -> t2) -> (g: t2 -> t3) -> (xs : List t1) -> 
    (ys : List t2) -> (zs : List t3) -> map f xs = ys -> map g ys = zs -> map (g . f) xs = zs
intermediateMapsCompose f g xs ys zs pf1 pf2 = rewrite sym (mapFusion g f xs) in rewrite pf1 in rewrite pf2 in Refl

mapPreservesNonEmpty : (f : a -> b) -> (xs : List a) -> NonEmpty xs -> NonEmpty (map f xs)
mapPreservesNonEmpty f [] IsNonEmpty impossible
mapPreservesNonEmpty f (y::ys) pf = IsNonEmpty
