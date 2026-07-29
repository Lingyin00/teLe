module Decide where

import Term
import LPO 
import Rewrite
import Huet 
import ExamplesFromKnuth
import Control.Exception (evaluate)
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

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

-- ====================================================================
data Theorem = Theorem
  { thNo       :: String
  , thName     :: String
  , thPrec     :: Prec
  , thAxioms   :: [Equation]
  , thGoal     :: Equation
  , thExpected :: Maybe Bool
  }

theorems :: [Theorem]
theorems =
  [ Theorem "1" "identity is unique" groupP'   uniquenessAxiom goalUniqueId  (Just True)
  , Theorem "2" "inverse is unique"  groupPinv uniqueInvAxiom  goalUniqueInv (Just True)
  ]

showAnswer :: Maybe Bool -> String
showAnswer (Just True)  = "yes"
showAnswer (Just False) = "no"
showAnswer Nothing      = "no CS"

runTheorem :: Theorem -> IO (Maybe Bool, Double)
runTheorem th = do
  t0  <- getCPUTime
  let out = decide (thPrec th) (thAxioms th) (thGoal th)
  _   <- evaluate (out == Just True)
  t1  <- getCPUTime
  pure (out, fromIntegral (t1 - t0) / 1e12)

runDecide :: IO Bool
runDecide = do
  printf "%-4s %-28s %-10s %-10s %8s\n"
         "#" "Theorem" "Result" "Expected" "time"
  putStrLn (replicate 64 '-')
  oks <- mapM row theorems
  putStrLn (replicate 64 '-')
  let n = length (filter not oks)
  printf "%d/%d matched\n" (length theorems - n) (length theorems)
  pure (n == 0)
  where
    row th = do
      (got, secs) <- runTheorem th
      let ok = got == thExpected th
      printf "%-4s %-28s %-10s %-10s %7.2fs%s\n"
             (thNo th) (thName th) (showAnswer got) (showAnswer (thExpected th))
             secs (if ok then "" else "   <-- MISMATCH")
      pure ok