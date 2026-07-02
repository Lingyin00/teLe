module ProblemA where

import Term
import Pretty
import LPO 
import Rewrite
import Huet
import CriticalPair
import Examples

-- SYN080+1 : Pelletier 58
-- axiom c4: f(X) = g(Y)   
synAx80 :: Equation
synAx80 = Equation
  (app "f" [var "x"])
  (app "g" [var "y"])

syn80Axioms :: [Equation]
syn80Axioms = [synAx80]

-- goal: f(f(X)) = f(g(Y))
goalSYN80 :: Equation
goalSYN80 = Equation
  (app "f" [app "f" [var "x"]])
  (app "f" [app "g" [var "y"]])

syn80Prec :: Prec
syn80Prec = precFromList ["f", "g"]

-- FAILED ORIENT: f(x) ≐ g(y) -- by using LPO
-- Nothing because new variables appears in the right hand side)