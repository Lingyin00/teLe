module Unification where

import Term
import Substitution
import Matching
import Data.Map (Map)
import qualified Data.Map as Map

-- compose of two Substitution
-- note that Subst is not a function but a data structure in my definition
compose :: Subst -> Subst -> Subst
compose f g = Map.union (Map.map (appSubst f) g) f -- Map.union in Haskell prefers left side

-- subsumption
isSubsump :: Term -> Term -> Bool
isSubsump t1 t2 = case match t1 t2 of
    Just _ -> True
    Nothing -> False

-- whether a variable x occurs in a term t
occursIn :: Var -> Term -> Bool
occursIn x (VarT y) = x == y
occursIn x (FunAppT _ ts) = any (occursIn x) ts

-- Unification algorithm: naive unification 
-- giving two terms s,t, try to compute a subsitution σ such that sσ = tσ
unify :: Term -> Term -> Maybe Subst
unify t1 t2 = go [(t1, t2)] Map.empty
    where
        go :: [(Term, Term)] -> Subst -> Maybe Subst
        go [] sigma = Just sigma
        go (eq : rest) sigma = case eq of
            (FunAppT f t1, FunAppT g t2)
              | f == g && length t1 == length t2 -> go (zip t1 t2 ++ rest) sigma -- rule: decompose
              | otherwise -> Nothing
            (VarT x, VarT y) | x == y -> go rest sigma -- rule: removal of trivial equations
            (VarT x, t) -- rule: elimination
              | occursIn x t -> Nothing 
              | otherwise -> 
                  let s = Map.singleton x t in 
                    go (map (\(a,b) -> (appSubst s a, appSubst s b)) rest) (compose s sigma)
            (t, VarT x)
              | occursIn x t -> Nothing
              | otherwise -> 
                  let s = Map.singleton x t in 
                    go (map (\(a,b) -> (appSubst s a, appSubst s b)) rest) (compose s sigma)

-- test
-- unify (app  "f" [x, x]) (app "f" [a, b])
-- unify x (app "f" [x])
-- unify (app "f" [x, x]) (app "f" [a, a])
-- unify (app "f" [x, y]) (app "f" [y, a])