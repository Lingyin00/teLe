module CriticalPair where

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
    pure (filter (\cp -> cpl cp /= cpr cp) cps) -- filter the trival critical pairs

--test
assoc :: Rule
assoc = Rule (app "f" [app "f" [var "x", var "y"], var "z"])
             (app "f" [var "x", app "f" [var "y", var "z"]])
-- printCPs (runFresh (criticalPairs assoc assoc)) 
-- result: f(_v0,f(_v1,_v2))  =?=  f(_v0,f(_v1,_v2)) -- this pair will disappear after filter
---------- f(f(_v3,f(_v4,_v1)),_v2)  =?=  f(f(_v3,_v4),f(_v1,_v2))

-- leftId: f(e, x) → x        
leftId :: Rule
leftId = Rule (app "f" [app "e" [], var "x"]) (var "x")
-- printCPs (runFresh (criticalPairs assoc leftId))
-- result : f(_v1,_v2)  =?=  f(e,f(_v1,_v2))
-- printCPs (runFresh (criticalPairs leftId assoc)) -- result : empty list
ruleF = Rule (app "f" [var "x"]) (var "x")
ruleG = Rule (app "g" [var "y"]) (var "y")
-- printCPs (runFresh (criticalPairs ruleF ruleG)) -- empty list


