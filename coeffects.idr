-- we want a coeffect system for idris, i.e. a datatype with the effectively an 
-- indexed comonad, with unit and bind/kleisli coextension etc.

interface Comonad (m : Type -> Type) where
    (>>=)  : (m a -> b) -> (m a) -> (m b)
    extract : (m a) -> a

mycoList: Type -> Type
mycoList t = List t

Comonad Main.mycoList where
    (>>=) f xm = map (\x => f [x])
    extract xs = head xs