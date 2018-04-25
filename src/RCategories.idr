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

record RComonadKleisli (obj : Type) (cat : RCategory obj) where
    constructor RComonadKleisliInfo
    mapping  : obj -> obj
    counit   : {a : obj} -> (mor cat) (mapping a) a
    coextend : {a, b : obj} -> (mor cat) (mapping a) b -> (mor cat) (mapping a) (mapping b)

record RIxComonad (obj : Type) (cat : RCategory obj) (ind : Type) where
    constructor RIxComonadInfo
    indcomon : (k : ind) -> RFunctor obj cat
    counit   : {a : obj} -> (k : ind) -> (mor cat) (func (indcomon k) a) a
    comult   : {a : obj} -> (k : ind) -> (mor cat) (func (indcomon k) a) (func (indcomon k) (func (indcomon k) a))

record RIxComonadKleisli (obj : Type) (cat : RCategory obj) (ind : Type) where
    constructor RIxComonadKleisliInfo
    mapping : (k : ind) -> obj -> obj
    counit   : {a : obj} -> (k : ind) -> (mor cat) (mapping k a) a
    coextend : {a, b : obj} -> (k : ind) -> (mor cat) (mapping k a) b -> (mor cat) (mapping k a) (mapping k b) 

record RIxCondComonad (obj : Type) (cat : RCategory obj) (ind : Type) (cond : ind -> Type) where
    constructor RIxCondComonadInfo
    indcomon : (k : ind) -> {pf : cond k} -> RFunctor obj cat
    counit   : {a : obj} -> (k : ind) -> {p : cond k} -> (mor cat) (func (indcomon k {pf = p}) a) a
    comult   : {a : obj} -> (k : ind) -> {p : cond k} -> 
        (mor cat) (func (indcomon k {pf = p}) a) (func (indcomon k {pf = p}) (func (indcomon k {pf = p}) a))

record RIxCondComonadKleisli (obj : Type) (cat : RCategory obj) (ind : Type) (cond : ind -> Type) where
    constructor RIxCondComonadKleisliInfo
    mapping : (k : ind) -> {pf : cond k} -> obj -> obj
    counit   : {a : obj} -> (k : ind) -> {p : cond k} -> (mor cat) (mapping k {pf = p} a) a
    coextend : {a, b : obj} -> (k : ind) -> {p : cond k} -> (mor cat) (mapping k {pf = p} a) b -> 
        (mor cat) (mapping k {pf = p} a) (mapping k {pf = p} b)
    
-- standardToKleisliForm : RComonad obj cat -> RComonadKleisli obj cat
-- standardToKleisliForm (RComonadInfo comon counit comult) = RComonadKleisliInfo (func comon) counit coextend
--         where   coextend : (x, y : obj) -> (mor cat) ((func comon) x) y -> (mor cat) ((func comon) x) ((func comon) y)
--                 coextend obj1 obj2 morph = 
--                     (comp cat) ((fmap comon) morph) comult

-- kleisliToStandardForm : RComonadKleisli obj cat -> RComonad obj cat
-- kleisliToStandardForm (RComonadKleisliInfo mapping counit coextend) = RComonadInfo (RFunctorInfo mapping ((\f => coextend ((comp cat) f counit)))) counit (coextend (idd cat))

-- IXstandardToKleisliForm : RIxComonad obj cat ind -> RIxComonadKleisli obj cat ind
-- IXstandardToKleisliForm (RIxComonadInfo indcomon counit comult) = RIxComonadKleisliInfo indcomon counit coextend
--     where   coextend : {x, y : obj} -> (k : ind) -> (mor cat) ((func (indcomon k)) x) y -> 
--                             (mor cat) ((func (indcomon k)) x) ((func (indcomon k)) y)
--             coextend k morph = (comp cat) ((fmap (indcomon k)) morph) (comult k)

-- IXCondStandardToKleisliForm : RIxCondComonad obj cat ind cond -> RIxCondComonadKleisli obj cat ind cond
-- IXCondStandardToKleisliForm (RIxCondComonadInfo indcomon counit comult) = RIxCondComonadKleisliInfo indcomon counit coextend
--         where   coextend : {x, y : obj} -> (k : ind) -> {p : cond k} ->
--                             (mor cat) ((func (indcomon k {pf = p})) x) y -> 
--                             (mor cat) ((func (indcomon k {pf = p})) x) ((func (indcomon k {pf = p})) y)
--                 coextend {x = ob1} {y = ob2} k morph = 
--                     let test = (fmap (indcomon k)) in ?hole
                -- testing : {x, y : obj} -> (k : ind) -> {p : cond k} ->
                --     (mor cat) ((func (indcomon k {pf = p})) x) y -> 
                --     (mor cat) ((func (indcomon k)) ((func (indcomon k)) x)) ((func (indcomon k)) y)
                -- testing {x = ob1} {y = ob2} k morph = (fmap (indcomon k)) morph

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
