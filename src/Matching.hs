module Matching where

import Term 
import Substitution
import Data.Map (Map)
import qualified Data.Map as Map

-- giving two terms s,t, try to compute a subsitution σ such that sσ = t

-- version without tail recursion
matching :: Term -> Term -> Maybe Subst
matching s t = go s t Map.empty
    where
        go :: Term -> Term -> Subst -> Maybe Subst
        -- Rule 4: {x → t} ∪ S ⇒ ⊥ if S contains x → t′with t ̸= t′
        go (VarT x) t' sigma = 
            case Map.lookup x sigma of
                Just a | a == t' -> Just sigma
                       | otherwise -> Nothing
                Nothing -> Just (Map.insert x t' sigma)
        -- Rule 3: function application cannot be matched to a variable
        go (FunAppT _ _) (VarT _) _ = Nothing
        -- Rule 2 and 1: function application matching to another function application
        go (FunAppT f tf) (FunAppT g tg) sigma 
          | f /= g = Nothing -- no substitution exists if their function symbols are different (Rule 2)
          | length tf /= length tg = Nothing -- different arity 
          | otherwise = goList (zip tf tg) sigma -- decompose
        goList :: [(Term, Term)] -> Subst -> Maybe Subst
        goList [] sigma = Just sigma
        -- The constraints on a variable are global across subterms, so they must all be accumulated into one shared substitution
        goList ((s,t) : rest) sigma = go s t sigma >>= goList rest

-- using tail recursion
match :: Term -> Term -> Maybe Subst
match s t = go [(s,t)] Map.empty
    where
        go :: [(Term,Term)] -> Subst -> Maybe Subst 
        go [] sigma = Just sigma
        go ((VarT x, t') : rest) sigma =
            case Map.lookup x sigma of
                Nothing -> go rest (Map.insert x t' sigma)
                Just a | a == t' -> go rest sigma
                       | otherwise -> Nothing
        go (((FunAppT _ _), (VarT _)) : _ ) _ = Nothing
        go (((FunAppT f tf), (FunAppT g tg)) : rest) sigma
            | f == g && length tf == length tg = 
                go (zip tf tg ++ rest) sigma
            | otherwise = Nothing

-- test
x = var "x"
y = var "y"
z = var "z"
a = app "a" []
b = app "b" []
f s t = app "f"[s, t]  
g s   = app "g" [s]
-- matching x a  ==>  Just {x ↦ a}
-- matching x (g a)  ==>  Just {x ↦ g(a)}
-- matching (f a b) (f a b)  ==>  Just {}
-- matching (f x y) (f a b)  ==>  Just {x ↦ a, y ↦ b}
-- matching (f x x) (f a a)  ==>  Just {x ↦ a}
-- matching (f x x) (f a b)  ==>  Nothing
-- matching (f a b) (g a)  ==>  Nothing
-- matching (g a) x  ==>  Nothing (in unification it could be x ↦ g(a))
-- matching x (g a)  ==>  Just {x ↦ g(a)}
-- matching (f x (g y)) (f a (g b))  ==>  Just {x ↦ a, y ↦ b}