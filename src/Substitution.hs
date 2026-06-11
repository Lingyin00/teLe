module Substitution where

import Term
import Data.Map (Map)
import qualified Data.Map as Map

-- a substitution σ : Var → Term, as a finite map
-- this data representation is better introspectable than Term -> Term
type Subst = Map Var Term

appSubst :: Subst -> Term -> Term
appSubst sub (VarT x) = 
    case Map.lookup x sub of -- using x as the key to lookup in the sub table
        Just t -> t
        Nothing -> VarT x
appSubst sub (FunAppT f ts) = FunAppT f (map (appSubst sub) ts)

-- σ = { x ↦ a, y ↦ g(b) }
testSub :: Subst
testSub = Map.fromList [(Var "x", app "a" []), (Var "y", app "g" [var "b"])]
-- appSubst testSub (app "f" [var "x", var "y"])