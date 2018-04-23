module RCategories

%access public export
%default total

record RCategory (obj : Type) where
    constructor RCategoryInfo
    mor  : obj -> obj -> Type
    idd  : {p : obj} -> mor p p
    comp : {a : obj} -> {b : obj} -> {c : obj} -> mor b c -> mor a b -> mor a c

record RFunctor (obj : Type) (cat : RCategory obj) where
    constructor RFunctorInfo
    func : obj -> obj
    fmap : {a : obj} -> {b : obj} -> (mor cat) a b -> (mor cat) (func a) (func b)
    
record RComonad (obj : Type) (cat : RCategory obj) where
    constructor RComonadInfo
    comon  : RFunctor obj cat
    counit : {a : obj} -> (mor cat) (func comon a) a
    comult : {a : obj} -> (mor cat) (func comon a) (func comon (func comon a))

record RIxComonad (obj : Type) (cat : RCategory obj) (ind : Type) where
    constructor RIxComonadInfo
    indcomon : (k : ind) -> RFunctor obj cat
    counit   : {a : obj} -> (k : ind) -> (mor cat) (func (indcomon k) a) a
    comult   : {a : obj} -> (k : ind) -> (mor cat) (func (indcomon k) a) (func (indcomon k) (func (indcomon k) a))

record RIxComonadKleisli (obj : Type) (cat : RCategory obj) (ind : Type) where
    constructor RIxComonadKleisliInfo
    indcomon : (k : ind) -> RFunctor obj cat
    counit   : {a : obj} -> (k : ind) -> (mor cat) (func (indcomon k) a) a
    coextend : {a, b : obj} -> (k : ind) -> (mor cat) (func (indcomon k) a) b -> (mor cat) (func (indcomon k) a) (func (indcomon k) b) 

record RIxCondComonad (obj : Type) (cat : RCategory obj) (ind : Type) (cond : ind -> Type) where
    constructor RIxCondComonadInfo
    indcomon : (k : ind) -> {pf : cond k} -> RFunctor obj cat
    counit   : {a : obj} -> (k : ind) -> {p : cond k} -> (mor cat) (func (indcomon k {pf = p}) a) a
    comult   : {a : obj} -> (k : ind) -> {p : cond k} -> 
        (mor cat) (func (indcomon k {pf = p}) a) (func (indcomon k {pf = p}) (func (indcomon k {pf = p}) a))

record RIxCondComonadKleisli (obj : Type) (cat : RCategory obj) (ind : Type) (cond : ind -> Type) where
    constructor RIxCondComonadKleisliInfo
    indcomon : (k : ind) -> {pf : cond k} -> RFunctor obj cat
    counit   : {a : obj} -> (k : ind) -> {p : cond k} -> (mor cat) ((func (indcomon k {pf = p})) a) a
    coextend : {a, b : obj} -> (k : ind) -> {p : cond k} -> (mor cat) (func (indcomon k {pf = p}) a) b -> 
        (mor cat) (func (indcomon k {pf = p}) a) ((func (indcomon k {pf = p})) b)

standardToKleisliForm : RIxCondComonad obj cat ind cond -> RIxCondComonadKleisli obj cat ind cond
standardToKleisliForm (RIxCondComonadInfo indcomon counit comult) = RIxCondComonadKleisliInfo indcomon counit coextend
        where coextend : {x, y : obj} -> (k : ind) -> {p : cond k} ->
                            (mor cat) ((func (indcomon k {pf = p})) x) y -> 
                            (mor cat) (func (indcomon k {pf = p}) x) ((func (indcomon k {pf = p})) y)
              coextend {x = ob1} {y = ob2} k morph = 
                let test = ((comp cat) {a = func (indcomon k) ob1} {b = func (indcomon k) (func (indcomon k) ob1)} {c = func (indcomon k) ob2}) 
                            (fmap (indcomon k) morph) (comult k) in ?hole

-- Categories with morphism application and object elements for checking of axioms
record RAppCategory (obj : Type) where
    constructor RAppCategoryInfo
    mor  : obj -> obj -> Type
    idd  : {p : obj} -> mor p p
    comp : {a : obj} -> {b : obj} -> {c : obj} -> mor b c -> mor a b -> mor a c
    el   : obj -> Type
    app  : {a : obj} -> {b : obj} -> (f : mor a b) -> (x : el a) -> el b

    idLeftIdentity  : {a : obj} -> {b : obj} -> (f : mor a b) -> (x : el a) -> app (comp f idd) x = app f x
    idRightIdentity : {a : obj} -> {b : obj} -> (f : mor a b) -> (x : el a) -> app (comp idd f) x = app f x
    compIsAccoc : {a : obj} -> {b : obj} -> {c : obj} -> {d : obj} -> (x: el a) ->
       (f : mor a b) -> (g : mor b c) -> (h : mor c d) -> app (comp h (comp g f)) x = app (comp (comp h g) f) x
