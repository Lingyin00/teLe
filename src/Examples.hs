module Examples where

import Term
import Pretty
import LPO 
import Rewrite
import Huet
import CriticalPair

-- This module checks several examples listed in the paper `Simple Word Problems in Universal Algebras`

-- 1. Group axioms, left (succeed)
groupP :: Prec
groupP = precFromList ["i", "f", "e"]

leftid, leftinv, associ :: Equation
leftid = Equation (app "f" [app "e" [], var "x"]) (var "x") -- left identity : e x = x
leftinv = Equation (app "f" [app "i" [var "x"], var "x"]) (app "e" []) -- left inverse : ix x = e
associ = Equation (app "f" [app "f" [var "x", var "y"], var "z"]) -- (x y) z = x (y z)
                (app "f" [var "x", app "f" [var "y", var "z"]])  

groupAxiom :: [Equation]
groupAxiom = [leftid, leftinv, associ]
testGroup :: Maybe [MRule]
testGroup = huet groupPrec groupAxiom
-- putStrLn (pretty testGroup)

-- 2. TODO: example 2 uses KBO

-- 3. Group axioms, right (succeed)
rightid, rightinv, assocr :: Equation
rightid = Equation (app "f" [var "x", app "e" []]) (var "x") -- x e = x
rightinv = Equation (app "f" [var "x", (app "i" [var "x"])]) (app "e" []) -- x ix = e
assocr = Equation (app "f" [app "f" [var "x", var "y"], var "z"]) -- (x y) z = x (y z)
                (app "f" [var "x", app "f" [var "y", var "z"]])
groupAxiomR = [rightid, rightinv, assocr]
testGroupR = huet groupPrec groupAxiomR
-- putStrLn (pretty testGroupR)

-- 4. Inverse property (succeed)
singleAx :: Equation
singleAx = Equation (app "f" [app "i" [var "a"], app "f" [var "a", var "b"]]) (var "b") -- ia (a b) = b
testSingleAx = huet groupPrec [singleAx]
-- putStrLn (pretty testSingleAx)
