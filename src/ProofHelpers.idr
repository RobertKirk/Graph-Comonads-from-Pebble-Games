module ProofHelpers

%access public export

data IsTrueBool : Bool -> Type where
    IsTrue : (True : Bool) -> IsTrueBool True

data IsFalseBool : Bool -> Type where
    IsFalse : (False : Bool) -> IsFalseBool False

data IsMappedList : (f: t1 -> t2) -> (xs : List t1) -> (ys : List t2) -> Type where
    IsEmptyMapList : IsMappedList f [] []
    IsConsMapList : IsMappedList f xs ys -> f x = y -> IsMappedList f (x::xs) (y::ys)
    IsFullMapList : map f xs = ys -> IsMappedList f xs ys

data IsElemOfList : (x : t) -> (ys : List t) -> Type where
    IsSingleElemList : IsElemOfList x [x]
    IsConsElemList : Either (x = y) (IsElemOfList x ys) -> IsElemOfList x (y::ys)

mapIdIsId : (xs: List t) -> map Basics.id xs = xs
mapIdIsId [] = Refl
mapIdIsId (x::xs) = let rec = mapIdIsId xs in rewrite rec in Refl
