module NonEmptyList

%access public export
%default total

infixr 9 :<:

data IsSucc : (n : Nat) -> Type where
    ItIsSucc : IsSucc (S n)
  
Uninhabited (IsSucc Z) where
    uninhabited ItIsSucc impossible
  
||| A decision procedure for `IsSucc`
isItSucc : (n : Nat) -> Dec (IsSucc n)
isItSucc Z = No absurd
isItSucc (S n) = Yes ItIsSucc

data NEList : (t : Type) -> Type where
    Singl : (x : t) -> NEList t
    (:<:) : (x : t) -> (xs : NEList t) -> NEList t

Eq t => Eq (NEList t) where
    (==) (Singl x) (Singl y) = x == y
    (==) (x:<:xs) (y:<:ys) =
        if x==y then xs==ys else False
    (==) _ _ = False

head : NEList t -> t
head (Singl x) = x
head (x:<:xs) = x   

last : NEList t -> t
last (Singl x) = x
last (x:<:xs) = last xs

length : NEList t -> Nat
length (Singl x) = 1
length (x:<:xs) = 1 + (length xs)

take : (n:Nat) -> {auto ok : IsSucc n} -> NEList t -> NEList t
take Z xs {ok = ItIsSucc} impossible
take (S Z) xs = Singl (head xs)
take (S (S n)) (Singl x) {ok = p} = Singl x
take (S (S n)) (x:<:xs)  {ok = p} = x :<: (take (S n) xs {ok = ItIsSucc})

drop : (n : Nat) -> (xs : NEList a) -> NEList a
drop Z     xs         = xs
drop (S n) (Singl x)  = Singl x
drop (S n) (x:<:xs)   = drop n xs

reverseOnto : NEList a -> NEList a -> NEList a
reverseOnto acc (Singl x) = x:<:acc
reverseOnto acc (x:<:xs) = reverseOnto (x:<:acc) xs

reverse : NEList a -> NEList a
reverse (Singl x) = Singl x
reverse (x:<:xs)  = reverseOnto (Singl x) xs

zipWith : (f : a -> b -> c) -> (l : NEList a) -> (r : NEList b) -> NEList c
zipWith f (Singl x) (ys) = Singl (f x (head ys))
zipWith f (x:<:xs) (Singl y) = Singl (f x y)
zipWith f (x:<:xs) (y:<:ys) = f x y :<: zipWith f xs ys

zip : (l : NEList a) -> (r : NEList b) -> NEList (a, b)
zip = zipWith (\x,y => (x, y))

map : (a -> b) -> NEList a -> NEList b
map f (Singl x) = Singl (f x)
map f (x:<:xs) = (f x):<:(map f xs)

inits : NEList a -> NEList (NEList a)
inits (Singl x) = Singl (Singl x)
inits (x:<:xs) = map (x :<:) (inits xs)

toList : NEList t -> List t
toList (Singl x) = [x]
toList (x:<:xs) = x :: (toList xs)

isPrefixOfBy : (eq : a -> a -> Bool) -> (left, right : NEList a) -> Bool
isPrefixOfBy p (Singl x) ys         = p x (head ys)
isPrefixOfBy p (x:<:xs) (Singl y)   = False
isPrefixOfBy p (x:<:xs) (y:<:ys)    = if (p x (head ys)) then isPrefixOfBy p xs ys else False

isPrefixOf : Eq a => NEList a -> NEList a -> Bool
isPrefixOf = isPrefixOfBy (==)

find : (a -> Bool) -> NEList a -> Maybe a
find p (Singl x) = if (p x) then Just x else Nothing
find p (x:<:xs) =
  if p x then
    Just x
  else
    find p xs

NEListIsNonEmpty : (ys : NEList t) -> NonEmpty (toList ys)
NEListIsNonEmpty (Singl x) = IsNonEmpty 
NEListIsNonEmpty (x:<:xs) = IsNonEmpty
