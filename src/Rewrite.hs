module Rewrite where

import Term
import Substitution
import Matching(match)
import Unification(unify)
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set

-- a rewrite rule l → r (structure)
data Rule = Rule {lhs :: Term, rhs :: Term}
    deriving (Eq, Ord, Show)

-- validity: ℓ ∉ X, and Var(rhs) ⊆ Var(lhs)
validRule :: Rule -> Bool
validRule (Rule l r) = notVar l && (vars r `Set.isSubsetOf` vars l)
  where
    notVar (VarT _) = False
    notVar _        = True

-- a term rewrite system (Σ, R)
data TRS = TRS {signature :: Signature, rules :: [Rule]}
    deriving (Show)

-- nonvariable positions : entrance to critical pair
nonVarPos :: Term -> [Pos]
nonVarPos t = [p | p <- positions t,
                    case subtermAt t p of
                        Just (VarT _) -> False
                        _ -> True]

-- fresh variable and renaming 
type Fresh = State Int

freshVar :: Fresh Term
freshVar = do -- get the current counter, add one,
    n <- get 
    put (n + 1) 
    pure (VarT (Var ("_v" ++ show n)))

-- get the computational result from state monad
runFresh :: Fresh a -> a
runFresh m = evalState m 0

-- renaming rule
renameRule :: Rule -> Fresh Rule
renameRule (Rule l r) = do
    let vs = Set.toList (vars l `Set.union` vars r)
    newVars <- mapM (const freshVar) vs 
    let sub = Map.fromList (zip vs newVars)
    pure (Rule (appSubst sub l) (appSubst sub r))

-- rewrite one step at a position, using one rule
rewriteAt :: Rule -> Pos -> Term -> Maybe Term
rewriteAt (Rule l r) p t = do
    s <- subtermAt t p
    m <- match l s
    replaceAt t p (appSubst m r)

-- any rewrite step
rewriteStep :: [Rule] -> Term -> Maybe Term
rewriteStep rs t = 
    case [t' | rule <- rs, p <- positions t, Just t' <- [rewriteAt rule p t]] of
    (t': _) -> Just t'
    []     -> Nothing

-- normalize to normal form
normalize :: [Rule] -> Term -> Term
normalize rs t = case rewriteStep rs t of
    Just t' -> normalize rs t'
    Nothing -> t

-- TODO：bidirectional rewriting of an equation

data Equation = Equation {eql :: Term, eqr :: Term}
    deriving (Eq, Ord, Show)

-- TODO : orient an equation by using term ordering