-- | 
-- SYN080+1 : Pelletier 58
-- axiom c4: f(X) = g(Y)   

module TPTP.Pelletier_syn0801 where

import Term
import Pretty
import LPO 
import Rewrite
import Huet

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

p0801 :: Prec
p0801 = precFromList ["f", "g"]

test0801 :: Maybe [MRule]
test0801 = huet p0801 syn80Axioms
result0801 :: IO ()
result0801 = putStrLn (pretty test0801)

-- ==============================================
-- result:
-- FAILED ORIENT: f(x) ≐ g(y) -- by using LPO
-- because new variables appears in the right hand side