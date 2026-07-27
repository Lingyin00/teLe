module Examples where

import Term
import LPO 
import Rewrite
import Huet

-- using the TRS to normalize equations
huetRules :: Maybe [MRule] -> Maybe [Rule]
huetRules = fmap (map mrule)

decideEq :: [Rule] -> Equation -> Bool
decideEq rs eq = normalize rs (eql eq) == normalize rs (eqr eq)

decide :: Prec -> [Equation] -> Equation -> Maybe Bool
decide p axioms goal =
    case huetRules(huet p axioms) of
        Nothing -> Nothing
        Just rs -> Just(decideEq rs goal)


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

-- this shoud return true
-- let Just rs = huetRules testGroup
goalRightInv :: Equation
goalRightInv = Equation (app "f" [var "x", app "i" [var "x"]]) (app "e" [])
-- decideEq rs goalRightInv

-- this should return false
goalComm :: Equation
goalComm = Equation (app "f" [var "x", var "y"]) (app "f" [var "y", var "x"])
-- decideEq rs goalComm

-- this should return true
goalRightId :: Equation
goalRightId = Equation (app "f" [var "x", app "e" []]) (var "x")
-- decideEq rs goalRightId


-- this should return true: 
goalInvProd :: Equation
goalInvProd = Equation (app "i" [app "f" [var "x", var "y"]])
                       (app "f" [app "i" [var "y"], app "i" [var "x"]])
-- decideEq rs goalInvProd

-- this should return true:
goalInv3 :: Equation
goalInv3 = Equation
  (app "i" [app "f" [var "x", app "f" [var "y", var "z"]]])
  (app "f" [app "i" [var "z"], app "f" [app "i" [var "y"], app "i" [var "x"]]])
-- decideEq rs goalInv3

-- this should return true:
goalConj :: Equation
goalConj = Equation
  (app "f" [ app "f" [var "z", app "f" [var "x", app "i" [var "z"]]]
           , app "f" [var "z", app "f" [app "i" [var "x"], app "i" [var "z"]]] ])
  (app "e" [])
-- decideEq rs goalConj

-- this should return false:
goalInvProdWrong :: Equation
goalInvProdWrong = Equation (app "i" [app "f" [var "x", var "y"]])
                            (app "f" [app "i" [var "x"], app "i" [var "y"]])

-- decideEq rs goalInvProdWrong

-- test for a proof
-- uniquess of identity element
leftidPrime :: Equation
leftidPrime = Equation (app "f" [app "e2" [], var "x"]) (var "x")
uniquenessAxiom :: [Equation]
uniquenessAxiom = groupAxiom ++ [leftidPrime]
groupP' :: Prec
groupP' = precFromList ["i", "f", "e", "e2"]
goalUniqueId :: Equation
goalUniqueId = Equation (app "e2" []) (app "e" [])
-- let Just rs1 = huetRules (huet groupP' uniquenessAxiom)
-- decideEq rs1 goalUniqueId

-- uniqueness of inverse element
leftinvPrime :: Equation
leftinvPrime = Equation (app "f" [app "a2" [], app "a" []]) (app "e" [])
uniqueInvAxiom :: [Equation]
uniqueInvAxiom = groupAxiom ++ [leftinvPrime]
groupPinv :: Prec
groupPinv = precFromList ["i", "f", "e", "a2", "a"]
goalUniqueInv :: Equation
goalUniqueInv = Equation (app "a2" []) (app "i" [app "a" []])
-- let Just rs2 = huetRules (huet groupPinv uniqueInvAxiom)
-- decideEq rs2 goalUniqueInv

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
