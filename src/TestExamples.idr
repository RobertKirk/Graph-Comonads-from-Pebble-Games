module TestExamples
import Data.Fin
import src.ProofHelpers

import src.RCategories
import src.Graphs
import src.Comonads

%default total

-- Graph Tests
lessthanmy : Rel Nat
lessthanmy (a,b) = a < b

implementation [myeq] Eq Nat where
    (==) a b = True

IntGraph : Graph
IntGraph = (Nat ** [1,2,3,4,5,6,7,8,9,10] ** lessthanmy ** myeq)