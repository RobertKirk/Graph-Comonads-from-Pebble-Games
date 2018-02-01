module Main

import Control.Category

-- Technically a multigraph or pseudograph
Graph : Type -> Type
Graph t = (List t, List (Int, List (t, t)))

Gmorph : Graph t -> Graph u -> Type
Gmorph g1 g2 = (t -> u, Int -> (t,t) -> Bool)

gid : Gmorph g1 g1
gid = (id, (\n => (\es => True)))

-- gap : Gmorph t u -> Graph t -> Graph u
-- gap (Gmor (vmap, emap)) (vs, ess) = 
--     (map vmap vs, 
--     map (\(n,es) => (n, map (\(u,v) => (vmap u, vmap v)) (filter (emap n) es))) ess
--     )

infixr 9 ..

(..) : Gmorph u v -> Gmorph t u -> Gmorph t v
(..) (vmap2, emap2) (vmap1, emap1) =
   (vmap2 . vmap1,
    (\n => 
        (\(t1, t2) => 
            case emap1 n (t1, t2) of
                True => emap2 n (vmap1 t1, vmap1 t2)
                False => False
        )
    ))

interface MyCategory (obj : Type) where
    constructor Categ
    mor : obj -> obj -> Type
    id  : mor p p
    (.) : mor u v -> mor t u -> mor t v

implementation MyCategory (Graph t) where
    mor = Gmorph
    id  = gid
    (.) = (..)