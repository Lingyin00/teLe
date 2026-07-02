module Assoc where

import Term
import Pretty
import LPO 
import Rewrite
import Huet
import CriticalPair
import Examples

-- SYN083+1 : 结合律蕴含四元广义结合律
-- 唯一公理 c4: f(X, f(Y,Z)) = f(f(X,Y), Z)
-- succeed
assocSYN :: Equation
assocSYN = Equation
  (app "f" [var "x", app "f" [var "y", var "z"]])
  (app "f" [app "f" [var "x", var "y"], var "z"])

synAxioms :: [Equation]
synAxioms = [assocSYN]

-- goal c1: f(X, f(Y, f(Z,W))) = f(f(f(X,Y),Z), W)
goalSYN :: Equation
goalSYN = Equation
  (app "f" [var "x", app "f" [var "y", app "f" [var "z", var "w"]]])
  (app "f" [app "f" [app "f" [var "x", var "y"], var "z"], var "w"])

synPrec :: Prec
synPrec = precFromList ["f"]