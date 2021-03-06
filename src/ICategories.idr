module ICategories

%access public export
%default total

interface ICategory (mor : obj -> obj -> Type) where
    idd  : {p:obj} -> mor p p
    comp : {a:obj} -> {b:obj} -> {c:obj} -> mor b c -> mor a b -> mor a c

    -- idLeftIdentity : (f: mor a b) -> (comp idd f) = f
    -- idRightIdentity : (f: mor a b) -> f = (comp idd f)
    -- compIsAccoc : (f : mor a b) -> (g : mor b c) -> (h : mor c d) -> comp h (comp g f) = comp (comp h g) f

interface ICategory morph => IFunctor (morph : obj -> obj -> Type) (f : obj -> obj) | f where
    fmap : {a:obj} -> {b:obj} -> morph a b -> morph (f a) (f b)

    -- fmapRespectsId : (a:obj) -> fmap (idd) = idd {p=a}

interface IFunctor morph m => IMonad (morph : obj -> obj -> Type) (m : obj -> obj) | m where
    unit : morph o (m o)
    multiplication : morph (m (m o)) (m o)

interface IFunctor morph t => IComonad (morph : obj -> obj -> Type) (t : obj -> obj) | m where
    counit : morph (t o) o
    comultiplication : morph (t o) (t (t o))

interface ICategory morph => IIxComonad (morph : obj -> obj -> Type) (t: k -> obj -> obj) | t where
    ixcounit : morph (t i o) o
    ixcomultiplication : morph (t i o) (t i (t i o))
