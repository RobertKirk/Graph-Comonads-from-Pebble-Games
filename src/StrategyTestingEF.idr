module StrategyTesting

import Data.Vect
import Data.Fin
import src.ProofHelpers
import src.NonEmptyList
import src.NonEmptyStream

import src.RCategories
import src.Graphs
import src.PebbleComonad
import src.EFComonad

%default total

getType : Structure sigma -> Type
getType (t ** _ ** _ ** _) = t

getList : EFplaysType n t -> List t
getList (MkPlays len xs) = toList xs

dimSwap : (List t1, List t2) -> List (t1, t2)
dimSwap ([], _) = []
dimSwap (_, []) = []
dimSwap ((x::xs), (y::ys)) = (x,y)::(assert_total (dimSwap (xs, ys)))

generateGamesEF : (rounds : Nat) -> {auto ok : IsSucc rounds} -> (sigma : Signature) -> (s1, s2 : Structure sigma) -> 
    StructMorph (EFComonadObj rounds s1) s2 -> NEList (List (getType s1, getType s2))
generateGamesEF Z {ok = ItIsSucc} s s1 s2 morph impossible
generateGamesEF (S k) {ok = p} sig (t1 ** vs1 ** interp1 ** eq1) (t2 ** vs2 ** interp2 ** eq2) morph = case (coextensionEF (S k) morph) of
    Smor mapping prof => (map (\pl => dimSwap (getList pl, getList (mapping pl))) (efplays (S k) vs1 ))

data Ex1Universe = One | Two | Three | Four

implementation [Ex1Equality] Eq Ex1Universe where
    (==) One One = True
    (==) Two Two = True
    (==) Three Three = True
    (==) Four Four = True
    (==) _ _ = False

ex1EqCorrect : (a, b : Ex1Universe) -> True = (==) @{Ex1Equality} a b -> a = b
ex1EqCorrect One One Refl = Refl
ex1EqCorrect One Two Refl impossible
ex1EqCorrect One Three Refl impossible
ex1EqCorrect One Four Refl impossible
ex1EqCorrect Two One Refl impossible
ex1EqCorrect Two Two Refl = Refl
ex1EqCorrect Two Three Refl impossible
ex1EqCorrect Two Four Refl impossible
ex1EqCorrect Three One Refl impossible
ex1EqCorrect Three Two Refl impossible
ex1EqCorrect Three Three Refl = Refl
ex1EqCorrect Three Four Refl impossible
ex1EqCorrect Four One Refl impossible
ex1EqCorrect Four Two Refl impossible
ex1EqCorrect Four Three Refl impossible
ex1EqCorrect Four Four Refl = Refl

Ex1Next : Ex1Universe -> Ex1Universe
Ex1Next One = Two
Ex1Next Two = Three
Ex1Next Three = Four
Ex1Next Four = One

ex1NextChanges : (a : Ex1Universe) -> Not (a = Ex1Next a)
ex1NextChanges One Refl impossible
ex1NextChanges Two Refl impossible
ex1NextChanges Three Refl impossible
ex1NextChanges Four Refl impossible

ex1NextChangesTwice : (a : Ex1Universe) -> Not (a = Ex1Next (Ex1Next a))
ex1NextChangesTwice One Refl impossible
ex1NextChangesTwice Two Refl impossible
ex1NextChangesTwice Three Refl impossible
ex1NextChangesTwice Four Refl impossible

ex1NoMutualNext : (a, b : Ex1Universe) -> True = (==) @{Ex1Equality} (Ex1Next a) b -> True = (==) @{Ex1Equality} (Ex1Next b) a -> Void
ex1NoMutualNext a b prf1 prf2 = 
    let p1 = ex1EqCorrect (Ex1Next a) b prf1 in let p2 = ex1EqCorrect (Ex1Next b) a prf2 in
    ex1NextChangesTwice a (sym (rewrite p1 in p2))

enumEx1Universe : NEList Ex1Universe
enumEx1Universe = listToNEL [One, Two, Three, Four]

Ex1Rel1 : Fin 1 -> Rel Ex1Universe
Ex1Rel1 FZ (One, Two) = True
Ex1Rel1 FZ (Two, Three) = True
Ex1Rel1 FZ (Three, Four) = True
Ex1Rel1 FZ _ = False

Ex1Rel2 : Fin 1 -> Rel Ex1Universe
Ex1Rel2 FZ (One, Two) = True
Ex1Rel2 FZ (Two, Three) = True
Ex1Rel2 FZ (Three, Four) = True
Ex1Rel2 FZ (Four, One) = True
Ex1Rel2 FZ _ = False

ex1rel1ImpliesNext : (a, b : Ex1Universe) -> True = Ex1Rel1 FZ (a, b) -> Ex1Next a = b
ex1rel1ImpliesNext One One Refl impossible
ex1rel1ImpliesNext One Two Refl = Refl
ex1rel1ImpliesNext One Three Refl impossible
ex1rel1ImpliesNext One Four Refl impossible
ex1rel1ImpliesNext Two One Refl impossible
ex1rel1ImpliesNext Two Two Refl impossible
ex1rel1ImpliesNext Two Three Refl = Refl
ex1rel1ImpliesNext Two Four Refl impossible
ex1rel1ImpliesNext Three One Refl impossible
ex1rel1ImpliesNext Three Two Refl impossible
ex1rel1ImpliesNext Three Three Refl impossible
ex1rel1ImpliesNext Three Four Refl = Refl
ex1rel1ImpliesNext Four One Refl impossible
ex1rel1ImpliesNext Four Two Refl impossible
ex1rel1ImpliesNext Four Three Refl impossible
ex1rel1ImpliesNext Four Four Refl impossible

ex1relTrueImpliesNotEqual : (a, b : Ex1Universe) -> True = Ex1Rel1 FZ (a, b) -> Not (True = (==) @{Ex1Equality} a b)
ex1relTrueImpliesNotEqual One One Refl prf2 impossible
ex1relTrueImpliesNotEqual One Two Refl Refl impossible
ex1relTrueImpliesNotEqual One Three Refl prf2 impossible
ex1relTrueImpliesNotEqual One Four Refl prf2 impossible
ex1relTrueImpliesNotEqual Two Two Refl prf2 impossible
ex1relTrueImpliesNotEqual Two One Refl prf2 impossible
ex1relTrueImpliesNotEqual Two Three Refl Refl impossible
ex1relTrueImpliesNotEqual Two Four Refl prf2 impossible
ex1relTrueImpliesNotEqual Three Three Refl prf2 impossible
ex1relTrueImpliesNotEqual Three One Refl prf2 impossible
ex1relTrueImpliesNotEqual Three Two Refl prf2 impossible
ex1relTrueImpliesNotEqual Three Four Refl Refl impossible
ex1relTrueImpliesNotEqual Four Four Refl prf2 impossible
ex1relTrueImpliesNotEqual Four One Refl prf2 impossible
ex1relTrueImpliesNotEqual Four Two Refl prf2 impossible
ex1relTrueImpliesNotEqual Four Three Refl prf2 impossible

ex2relTrueImpliesNotEqual : (a, b : Ex1Universe) -> True = Ex1Rel2 FZ (a, b) -> Not (True = (==) @{Ex1Equality} a b)
ex2relTrueImpliesNotEqual One One Refl prf2 impossible
ex2relTrueImpliesNotEqual One Two Refl Refl impossible
ex2relTrueImpliesNotEqual One Three Refl prf2 impossible
ex2relTrueImpliesNotEqual One Four Refl prf2 impossible
ex2relTrueImpliesNotEqual Two Two Refl prf2 impossible
ex2relTrueImpliesNotEqual Two One Refl prf2 impossible
ex2relTrueImpliesNotEqual Two Three Refl Refl impossible
ex2relTrueImpliesNotEqual Two Four Refl prf2 impossible
ex2relTrueImpliesNotEqual Three Three Refl prf2 impossible
ex2relTrueImpliesNotEqual Three One Refl prf2 impossible
ex2relTrueImpliesNotEqual Three Two Refl prf2 impossible
ex2relTrueImpliesNotEqual Three Four Refl Refl impossible
ex2relTrueImpliesNotEqual Four Four Refl prf2 impossible
ex2relTrueImpliesNotEqual Four One Refl Refl impossible
ex2relTrueImpliesNotEqual Four Two Refl prf2 impossible
ex2relTrueImpliesNotEqual Four Three Refl prf2 impossible

Ex1Structure1 : Structure 1
Ex1Structure1 = (Ex1Universe ** enumEx1Universe ** Ex1Rel1 ** Ex1Equality)

Ex1Structure2 : Structure 1
Ex1Structure2 = (Ex1Universe ** enumEx1Universe ** Ex1Rel2 ** Ex1Equality)

Ex1plays : NEList (EFplaysType 2 Ex1Universe)
Ex1plays = efplays 2 enumEx1Universe

Ex1Strategy : EFplaysType 2 Ex1Universe -> Ex1Universe
Ex1Strategy (MkPlays (FS FZ) [x]) = One
Ex1Strategy (MkPlays (FS (FS FZ)) [x, y]) with ((==) @{Ex1Equality} (Ex1Next x) y, (==) @{Ex1Equality} (Ex1Next y) x) 
    | (False, False) = Three
    | (False, True)  = Four
    | (True, False)  = Two
    | (True, True)   = One

intStratProof1 : Ex1Next xl = y -> y' = x -> a = (==) @{Ex1Equality} (Ex1Next xl) x -> a = (==) @{Ex1Equality} y y'
intStratProof1 prf1 prf2 prf3 = rewrite sym prf1 in (rewrite prf2 in prf3)

intStratProof2 : (y : Ex1Universe) -> a = (==) @{Ex1Equality} y y -> a = True
intStratProof2 One prf = prf
intStratProof2 Two prf = prf
intStratProof2 Three prf = prf
intStratProof2 Four prf = prf

intStratProof3 : Ex1Next y = xl -> y = x -> a = (==) @{Ex1Equality} (Ex1Next x) xl' -> a = (==) @{Ex1Equality} xl xl'
intStratProof3 prf1 prf2 prf3 = rewrite sym prf1 in rewrite prf2 in prf3

stratProof : (a : EFplaysType 2 Ex1Universe) -> (b : EFplaysType 2 Ex1Universe) -> 
    (True = efRel @{Ex1Equality} (Ex1Rel1 FZ) (a, b)) -> True = Ex1Rel2 FZ (Ex1Strategy a, Ex1Strategy b)
stratProof (MkPlays (FS FZ) [x]) (MkPlays (FS FZ) [y]) prf = 
    let contra = ex1relTrueImpliesNotEqual x y (conjunctsTrueL prf) in 
    let diction = conjunctsTrueL (conjunctsTrueR {b = ((==) @{Ex1Equality} x y && True)} prf) in void (contra diction)
stratProof (MkPlays (FS (FS FZ)) (x::[xl])) (MkPlays (FS FZ) [y]) prf with ((==) @{Ex1Equality} (Ex1Next x) xl, (==) @{Ex1Equality} (Ex1Next xl) x) proof p
    | (False, False) = 
        let x1 = conjunctsTrueL {a = Ex1Rel1 FZ (xl, y)} prf in 
        let x1' = ex1rel1ImpliesNext xl y x1 in
        let x2 = ex1EqCorrect y x (conjunctsTrueL {a = (==) @{Ex1Equality} y x} (conjunctsTrueR {b = ((==) @{Ex1Equality} y x && True)} prf)) in
        let x3 = pairsSplitR p in
        let test = intStratProof1 x1' x2 x3 in sym (intStratProof2 y test)
    | (False, True)  = Refl
    | (True, False)  = 
        let x1 = conjunctsTrueL {a = Ex1Rel1 FZ (xl, y)} prf in 
        let x1' = ex1rel1ImpliesNext xl y x1 in
        let x2 = ex1EqCorrect y x (conjunctsTrueL {a = (==) @{Ex1Equality} y x} (conjunctsTrueR {b = ((==) @{Ex1Equality} y x && True)} prf)) in
        let x3 = pairsSplitR p in
        let test = intStratProof1 x1' x2 x3 in sym (intStratProof2 y test)
    | (True, True)   = void (ex1NoMutualNext x xl (pairsSplitL p) (pairsSplitR p))
stratProof (MkPlays (FS FZ) [y]) (MkPlays (FS (FS FZ)) (x::[xl])) prf with ((==) @{Ex1Equality} (Ex1Next x) xl, (==) @{Ex1Equality} (Ex1Next xl) x) proof p
    | (False, False) = 
        let x1 = conjunctsTrueL {a = Ex1Rel1 FZ (y, xl)} prf in 
        let x1' = ex1rel1ImpliesNext y xl x1 in
        let x2 = ex1EqCorrect y x (conjunctsTrueL {a = (==) @{Ex1Equality} y x} (conjunctsTrueR {b = ((==) @{Ex1Equality} y x && True)} prf)) in
        let x3 = pairsSplitL p in
        let test = intStratProof3 x1' x2 x3 in sym (intStratProof2 xl test)
    | (False, True)  = 
        let x1 = conjunctsTrueL {a = Ex1Rel1 FZ (y, xl)} prf in 
        let x1' = ex1rel1ImpliesNext y xl x1 in
        let x2 = ex1EqCorrect y x (conjunctsTrueL {a = (==) @{Ex1Equality} y x} (conjunctsTrueR {b = ((==) @{Ex1Equality} y x && True)} prf)) in
        let x3 = pairsSplitL p in
        let test = intStratProof3 x1' x2 x3 in sym (intStratProof2 xl test)
    | (True, False)  = Refl
    | (True, True)   = void (ex1NoMutualNext x xl (pairsSplitL p) (pairsSplitR p))
stratProof (MkPlays (FS (FS FZ)) (x::[xl])) (MkPlays (FS (FS FZ)) (y::[yl])) prf = 
    let x1 = ex1rel1ImpliesNext xl yl (conjunctsTrueL prf {a = Ex1Rel1 FZ (xl, yl)}) in
    let x2 = ex1EqCorrect xl yl (conjunctsTrueL (conjunctsTrueR (conjunctsTrueR prf))) in
    void (ex1NextChanges xl (sym (trans x1 (sym x2))))

Ex1StrategyMorph : StructMorph (EFComonadObj 2 Ex1Structure1) Ex1Structure2
Ex1StrategyMorph = Smor Ex1Strategy (ItIsStructMorph prf)
        where prf : (k : Fin 1) -> IsGraphMorph Ex1Strategy (efInterp @{Ex1Equality} 2 Ex1Rel1 k) (Ex1Rel2 k)
              prf FZ = IsGraphMorphByElem stratProof

Ex1Games : NEList (List (Ex1Universe, Ex1Universe))
Ex1Games = generateGamesEF 2 1 Ex1Structure1 Ex1Structure2 Ex1StrategyMorph
