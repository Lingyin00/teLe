module Rewrite where

import Term 
import Substitution
import qualified Data.Set as Set

-- a rewrite rule l → r (structure)
data Rule = Rule {lhs : Term, rhs : Term}
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

-- TODO: rewrite steps, rewrite to normal form, etc...