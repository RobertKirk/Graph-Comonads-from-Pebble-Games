-- module Main

-- import Data.Vect
-- import Data.Fin

-- -- Generally, I've had to use Fin (S(k)) for the pebble numbers, and then ignore the 0 and start at 1. Also to cover cases I've most 
-- -- defined functions on the empty set of plays, even though we don't accept that in the universe of Tk (A)

-- -- necessary for building well but does nothing
-- main : IO ()
-- main = putStrLn "Hello world"

-- -- Helpers
-- data MaybeInf = Inf | Finite Nat

-- vectToList: Vect n a -> List a
-- vectToList Nil = []
-- vectToList (x::xs) = (x::(vectToList(xs)))

-- --Model Theory Definitions
-- Signature: Type
-- Signature = (List String, String -> Nat)

-- --Currently only have 2-argument relations
-- Interpretation: Type -> Type
-- Interpretation t = String -> Vect 2 t -> Bool

-- --"Infinite" lists need some explicit Lazy construction which I haven't added here, but probably could be (and then factored through 
-- -- the rest of the types)
-- Universe: MaybeInf -> Type -> Type
-- Universe Inf t = List t
-- Universe (Finite n) t = Vect n t

-- Structure: Signature -> MaybeInf -> Type ->  Type
-- Structure s mbi t = (Universe mbi t, Signature, Interpretation t)

-- -- Toy Examples of above definitions
-- arity1 : String -> Nat
-- arity1 s = case s of
-- "r1" => 2
-- "r2" => 2
-- "r3" => 2
-- _ => 0

-- interp: Interpretation (Fin 10)
-- interp s = case s of
-- "r1" => (\(x::y::Nil) => x < y)
-- "r2" => (\(x::y::Nil) => x > y)
-- "r3" => (\(x::y::Nil) => x == y)
-- _ => (\_ => False)

-- signa1: Signature
-- signa1 = (["r1", "r2", "r3"], arity1)

-- signa2: Signature
-- signa2 = (["r2", "r1", "r3"], arity1)

-- struct1: Structure Main.signa1 (Main.Finite 9) (Fin 10)
-- struct1 = ((0::(1::(2::(3::(4::(5::(6::(7::(8::Nil))))))))), signa1, interp)

-- struct2: Structure Main.signa2 (Main.Inf) (Fin 10)
-- struct2 = ([0..9], signa2, interp)

-- -- type of list of plays for a pebble number k (using Fin S(K) as Fin is numbers strictly less than the argument)
-- playsType: Nat -> Type -> Type
-- playsType k t = List (Fin (S(k)), t)

-- -- a helper unit typed to enable conversion from Nat to Fin
-- myUnit: Fin (S(n))
-- myUnit = 0

-- -- generating all possible plays of exactly a certain length, depending on whether the universe is finite or "infinite"
-- playsNInf: Nat -> Universe Inf t -> (peb:Nat) -> List (playsType peb t)
-- playsNInf _ u Z = [[]]
-- playsNInf Z u _ = [[]]
-- playsNInf (S(n)) u (S(k)) = [(p++[(j, xi)]) |   p<-(playsNInf n u (S(k))),
--                                         xi<-u,
--                                         j<-(map (\v => fromMaybe myUnit (Data.Fin.natToFin v (S(S(k)))) ) [0..(S(k))]) ]

-- playsNFin: Nat -> Universe (Finite n) t -> (peb:Nat) -> List (playsType peb t)
-- playsNFin _ u Z = [[]]
-- playsNFin Z u _ = [[]]
-- playsNFin (S(n)) u (S(k)) = [(p++[(j, xi)]) |   p<-(playsNFin n u (S(k))),
--                                         xi<-(vectToList u),
--                                         j<-(map (\v => fromMaybe myUnit (Data.Fin.natToFin v (S(S(k)))) ) [0..(S(k))]) ]

-- playsPrefix: Eq t => playsType k t -> playsType k t -> Fin 3 --0 for neither, 1 for ps =< qs, 2 for qs =< ps
-- playsPrefix ps qs = 
-- if (List.isPrefixOf ps qs) then 1 
-- else if (List.isPrefixOf qs ps) then 2 
-- else 0

-- --epsilon and delta counit and comultiplication
-- epsilonA: (playsType k t) -> t
-- epsilonA (arg::args) = snd (last (arg::args))

-- deltaARec: Nat -> (playsType k t) -> (playsType k t) -> (playsType k (playsType k t))
-- deltaARec k [] _ = []
-- deltaARec k (play::plays) toplay = (fst play, take k toplay)::(deltaARec (S(k)) plays toplay)

-- deltaA: (playsType k t) -> (playsType k (playsType k t))
-- deltaA [] = []
-- deltaA (play::plays) = deltaARec (S(Z)) (play::plays) (play::plays)

-- -- extending an interpretation on a structure's universe to one on it's comonadified universe (the universe of plays with a set 
-- -- number of pebbles)
-- interpretationExtend: Eq t => (Interpretation t)-> (Interpretation (playsType k t))
-- interpretationExtend i = \rs => (\((a1::args1)::(a2::args2)::Nil) => case (playsPrefix (a1::args1) (a2::args2)) of
-- FZ => False
-- FS FZ => 
-- if(isNothing (find (== last (a1::args1)) (a2::args2))) then
--     (i rs ((epsilonA (a1::args1))::((epsilonA (a2::args2))::Nil)))
-- else False
-- FS (FS FZ) => 
-- if(isNothing (find (== last (a2::args2)) (a1::args1))) then
--     (i rs ((Basics.snd (last (a2::args2)))::(Basics.snd (last (a1::args1)))::Nil))
-- else False
-- )

-- -- The comonad's operation on Objects of the Structure Category (i.e. structures)
-- TkObj: Eq t => (k:Nat) -> (Structure s Inf t) -> (Structure s Inf (playsType k t))
-- TkObj Z (u, s, i) = ([], s, interpretationExtend i)
-- TkObj (S(k)) (u, s, i) = (join [playsNInf n u (S(k)) | n <- [1..(S(k))]], s, interpretationExtend i)
--                                                 -- here we only take finte length plays as Idris is eager evaluation,
--                                                 -- could later try to use Lazy constructor to make this possibly infinite

-- TkMorph: (k:Nat) -> (a -> b) -> (playsType k a) -> (playsType k b)
-- TkMorph k f plays = map (\(p,o) => (p, f(o))) plays

-- -- we claim (TkObj V TkMorph, epsilonA, deltaA) form a comonad

-- -- f |-> f*
-- kleisliCoextend: (k:Nat) -> ((playsType k a) -> b) -> (playsType k a) -> (playsType k b)
-- kleisliCoextend k f plays = (TkMorph k f) (deltaA plays)
