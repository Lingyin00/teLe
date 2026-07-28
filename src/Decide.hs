module Decide where

import Term
import LPO 
import Rewrite
import Huet 
import ExamplesFromKnuth

-- ======================================================================
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

-- ========================================================================
-- Theroem 1. uniqueness of the identity
--    a second left identity e2 must be equal to e
leftidPrime :: Equation
leftidPrime = Equation (app "f" [app "e2" [], var "x"]) (var "x")

uniquenessAxiom :: [Equation]
uniquenessAxiom = groupAxiom ++ [leftidPrime]

groupP' :: Prec
groupP' = precFromList ["i", "f", "e", "e2"]

goalUniqueId :: Equation
goalUniqueId = Equation (app "e2" []) (app "e" [])

-- expected: Just True
resultUniqueId :: Maybe Bool
resultUniqueId = decide groupP' uniquenessAxiom goalUniqueId

-- ========================================================================
-- Theorem 2. uniqueness of the inverse
--    if a2 is a left inverse of a, then a2 = i(a)
leftinvPrime :: Equation
leftinvPrime = Equation (app "f" [app "a2" [], app "a" []]) (app "e" [])

uniqueInvAxiom :: [Equation]
uniqueInvAxiom = groupAxiom ++ [leftinvPrime]

groupPinv :: Prec
groupPinv = precFromList ["i", "f", "e", "a2", "a"]

goalUniqueInv :: Equation
goalUniqueInv = Equation (app "a2" []) (app "i" [app "a" []])

-- expected: Just True
resultUniqueInv :: Maybe Bool
resultUniqueInv = decide groupPinv uniqueInvAxiom goalUniqueInv