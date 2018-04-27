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

getType : Structure sigma -> Type
getType (t ** _ ** _ ** _) = t

getList : EFplaysType n t -> List t
getList (MkPlays len xs) = toList xs

dimSwap : (List t1, List t2) -> List (t1, t2)
dimSwap ([], _) = []
dimSwap (_, []) = []
dimSwap ((x::xs), (y::ys)) = (x,y)::(dimSwap (xs, ys))

generateGamesEF : (rounds : Nat) -> {auto ok : IsSucc rounds} -> (sigma : Signature) -> (s1, s2 : Structure sigma) -> 
    StructMorph (EFComonadObj rounds s1) s2 -> NEStream (List (getType s1, getType s2))
generateGamesEF Z {ok = ItIsSucc} s s1 s2 morph impossible
generateGamesEF (S k) {ok = p} sig (t1 ** vs1 ** interp1 ** eq1) (t2 ** vs2 ** interp2 ** eq2) morph = case (coextensionEF (S k) morph) of
    Smor mapping prof => (map (\pl => dimSwap (getList pl, getList (mapping pl))) (efplays (S k) vs1 ))

data Ex1Universe = One | Two | Three | Four

Ex1Next : Ex1Universe -> Ex1Universe
Ex1Next One = Two
Ex1Next Two = Three
Ex1Next Three = Four
Ex1Next Four = One

enumEx1Universe : NEStream Ex1Universe
enumEx1Universe = listToNEStream [One, Two, Three, Four]

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

[Ex1Equality] Eq Ex1Universe where
    (==) One One = True
    (==) Two Two = True
    (==) Three Three = True
    (==) Four Four = True
    (==) _ _ = False

Ex1Structure1 : Structure 1
Ex1Structure1 = (Ex1Universe ** enumEx1Universe ** Ex1Rel1 ** Ex1Equality)

Ex1Structure2 : Structure 1
Ex1Structure2 = (Ex1Universe ** enumEx1Universe ** Ex1Rel2 ** Ex1Equality)

Ex1plays : NEStream (EFplaysType 2 Ex1Universe)
Ex1plays = efplays 2 enumEx1Universe

Ex1Strategy : Eq Ex1Universe => getType (EFComonadObj 2 Ex1Structure1) -> Ex1Universe
Ex1Strategy (MkPlays (FS FZ) [x]) = One
Ex1Strategy (MkPlays (FS (FS FZ)) [x, y]) = 
    if ((Ex1Next x) == y) then Two else 
    if ((Ex1Next y)) == x then Four else
    Three

Ex1StrategyMorph : Eq Ex1Universe => StructMorph (EFComonadObj 2 Ex1Structure1) Ex1Structure2
Ex1StrategyMorph = ?hole