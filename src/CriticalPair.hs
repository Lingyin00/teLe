module CriticalPair where

import LPO
import Unification
import Rewrite
import Term (Term)
import Substitution

-- documents where and how the critical pair comes from
-- TODO: extension for later use (Proof reconstruction)
-- Or it need a better data structure(decision for later)
data Source = FromOverlap Rule Rule Subst 
    deriving (Show) -- FromOverlap :: Rule -> Rule -> Subst -> Source

data CriticalPair = CriticalPair{
    cpl :: Term,
    cpr :: Term,
    cpSource :: Source
} deriving (Show)




