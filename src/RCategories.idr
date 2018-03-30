module RCategories

%access public export
%default total

record RCategory (obj : Type) where
    constructor RCategoryInfo
    mor  : obj -> obj -> Type
    idd  : {p: obj} -> mor p p
    comp : {a : obj} -> {b : obj} -> {c : obj} -> mor b c -> mor a b -> mor a c
    --idLeftIdentity : {a: obj} -> {b: obj} -> (f: mor a b) -> (comp idd f) = f
    --idRightIdentity : {a: obj} -> {b: obj} -> (f: mor a b) -> f = (comp idd f)
    --compIsAccoc : {a: obj} -> {b: obj} -> {c : obj} -> {d : obj} -> 
    --    (f : mor a b) -> (g : mor b c) -> (h : mor c d) -> comp h (comp g f) = comp (comp h g) f

record RFunctor (obj: Type) (cat : RCategory obj) where
    constructor RFunctorInfo
    func : obj -> obj
    fmap : {a : obj} -> {b : obj} -> (mor cat) a b -> (mor cat) (func a) (func b)
    --fmapRespectsId : (a : obj) -> fmap ((idd cat)) = (idd cat)

record RComonad (obj : Type) (cat : RCategory obj) where
    constructor RComonadInfo
    comon  : RFunctor obj cat
    counit : {a : obj} -> (mor cat) a ((func comon) a)
    comult : {a : obj} -> (mor cat) ((func comon) a) ((func comon) ((func comon) a))

record RIxComonad (obj : Type) (cat : RCategory obj) (ind: Type) where
    constructor RIxComonadInfo
    indcomon : ind -> RFunctor obj cat
    counit   : {a : obj} -> {k : ind} -> (mor cat) ((func (indcomon k)) a) a
    comult   : {a : obj} -> {k : ind} -> (mor cat) ((func (indcomon k)) a) ((func (indcomon k)) ((func (indcomon k)) a))
