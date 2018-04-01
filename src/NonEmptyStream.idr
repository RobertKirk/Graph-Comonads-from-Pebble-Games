module NonEmptyStream

%access public export
%default total

infixr 9 :>:

data NEStream : (elem : Type) -> Type where
    Sing : (x : elem) -> NEStream elem
    (:>:) : (x : elem) -> (xs : Inf (NEStream elem)) -> NEStream elem

head : NEStream k -> k
head (Sing x) = x
head (x:>:xs) = x

tail : NEStream k -> NEStream k
tail (Sing x) = Sing x
tail (x:>:xs) = xs

map : (a -> b) -> NEStream a -> NEStream b
map f (Sing x) = Sing (f x)
map f (x:>:xs) = ((f x):>:(map f xs))

iterate : (a -> a) -> a -> NEStream a
iterate f x = x :>: iterate f (f x)

zipWith : (a -> b -> c) -> (NEStream a) -> (NEStream b) -> NEStream c
zipWith f (Sing x) ys = Sing (f x (head ys))
zipWith f xs (Sing y) = Sing (f (head xs) y)
zipWith f (x:>:xs) (y:>:ys) = f x y :>: zipWith f xs ys

zip : NEStream a -> NEStream b -> NEStream (a, b)
zip = zipWith (\x,y => (x,y))

listToNEStream : (xs:List a) -> {auto ok : NonEmpty xs} -> NEStream a
listToNEStream [] {ok=IsNonEmpty} impossible
listToNEStream [x] {ok=p} = Sing x
listToNEStream (x::y::ys) {ok=p} = x:>:(listToNEStream {ok = IsNonEmpty} (y::ys))

concatNESofList : t -> NEStream (List t) -> NEStream t
concatNESofList unit (Sing []) = Sing unit
concatNESofList unit (Sing [x]) = Sing x
concatNESofList unit (Sing (x::y::xs)) = x :>: (assert_total (concatNESofList unit (Sing (y::xs))))
concatNESofList unit (x:>:xs) = case x of
        []          => assert_total (concatNESofList unit xs)
        [z]         =>  z :>: (assert_total (concatNESofList unit xs))
        z::y::ys    => z :>: (assert_total (concatNESofList unit ((y::ys):>:xs)))

--Examples
mystream : NEStream Nat
mystream = 1 :>: 2 :>: 3 :>: 4 :>: Sing 1

ones : NEStream Nat
ones = 1 :>: ones

twos : NEStream Nat
twos = map (\x => 2*x) ones

doubles : NEStream Nat
doubles = iterate (\x => x*2) 1