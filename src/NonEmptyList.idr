module NonEmptyList
import src.ProofHelpers

%access public export
%default total

data NEList : (t : Type) -> Type where
    NEL : (xs : List t) -> {auto ok : NonEmpty xs} -> NEList t

map : (a -> b) -> NEList a -> NEList b
map f (NEL xs {ok = pf}) = NEL (map f xs) {ok = mapPreservesNonEmpty f xs pf}

-- concat : NEList (NEList t) -> NEList t
-- concat (NEL [] {ok = IsNonEmpty}) impossible
-- concat (NEL (NEL [] {ok = IsNonEmpty})::xs) impossible
-- concat (NEL ((NEL (y::ys))::xs)) = 
