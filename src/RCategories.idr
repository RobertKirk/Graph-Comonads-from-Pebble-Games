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
