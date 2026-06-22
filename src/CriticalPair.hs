module CriticalPair where

import LPO
import Unification
import Rewrite
import Term 
import Substitution

-- documents where and how the critical pair comes from
-- TODO: extension for later use (Proof reconstruction)
-- Or it need a better data structure(decision for later)
data Source = FromOverlap Rule Rule Pos Subst 
    deriving (Show) -- FromOverlap :: Rule -> Rule -> Subst -> Source

data CriticalPair = CriticalPair{
    cpl :: Term,
    cpr :: Term,
    cpSource :: Source
} deriving (Show)

-- given two rules, compute its critical pair 
criticalPairs :: Rule -> Rule -> Fresh [CriticalPair]
criticalPairs r1 r2 = do
    r1' <- renameRule r1 
    r2' <- renameRule r2 
    let s = lhs r1'
        t = rhs r1'
        u = lhs r2'
        v = rhs r2'
        cps = [CriticalPair left right (FromOverlap r2' r1' pos sub) |
               pos <- nonVarPos s,
               Just subterm <- [subtermAt s pos],
               Just sub <- [unify u subterm],
               let right = appSubst sub t,
               Just left <- [replaceAt (appSubst sub s) pos (appSubst sub v)]]
    pure cps

--test
assoc :: Rule
assoc = Rule (app "f" [app "f" [var "x", var "y"], var "z"])
             (app "f" [var "x", app "f" [var "y", var "z"]])
-- runFresh (criticalPairs assoc assoc)


