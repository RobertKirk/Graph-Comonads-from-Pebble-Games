module Categories

%access public export

interface Category (mor : obj -> obj -> Type) where
    id  : {p:obj} -> mor p p
    (.) : {a:obj} -> {b:obj} -> {c:obj} -> mor b c -> mor a b -> mor a c

interface Category morph => Functor (morph : obj -> obj -> Type) (f : obj -> obj) | f where
    fmap : morph a b -> morph (f a) (f b)

interface Functor morph m => Monad (morph : obj -> obj -> Type) (m : obj -> obj) | m where
    unit : morph o (m o)
    multiplication : morph (m (m o)) (m o)

interface Functor morph t => Comonad (morph : obj -> obj -> Type) (t : obj -> obj) | m where
    counit : morph (t o) o
    comultiplication : morph (t o) (t (t o))

interface Category morph => IxComonad (morph : obj -> obj -> Type) (t: k -> obj -> obj) where
    ixcounit : morph (t i o) o
    ixcomultiplication : morph (t i o) (t i (t i o))