module testUnify where

import Test.QuickCheck
import qualified Data.Map as Map
import Term
import Substitution
import Unification

-- Random Term generator: small variable/symbol domains so that s and t
-- are likely to share variables, which is what actually exercises propagation
instance Arbitrary Term where
  arbitrary = sized go
    where
      go 0 = VarT <$> genVar
      go n = frequency
        [ (1, VarT <$> genVar)
        , (2, FunAppT <$> genFun <*> scaledList n)
        ]
      scaledList n = do
        k <- choose (0, 3)                 -- arity 0–3 (0 means a constant)
        vectorOf k (go (n `div` 2))
      genVar = Var     <$> elements ["x", "y", "z"]
      genFun = FuncSym <$> elements ["f", "g", "a", "b"]

-- soundness: if unify succeeds, the returned substitution really makes both sides equal
prop_unify_sound :: Term -> Term -> Bool
prop_unify_sound s t = case unify s t of
  Just sigma -> appSubst sigma s == appSubst sigma t
  Nothing    -> True

-- any term unifies with itself (catches the "should succeed but fails" cases soundness misses)
prop_unify_self :: Term -> Bool
prop_unify_self t = case unify t t of
  Just _  -> True
  Nothing -> False

-- idempotence: σ(σ(s)) == σ(s), catches incomplete propagation (e.g. x↦y while y is also bound)
prop_idempotent :: Term -> Term -> Bool
prop_idempotent s t = case unify s t of
  Just sigma -> appSubst sigma (appSubst sigma s) == appSubst sigma s
  Nothing    -> True

main :: IO ()
main = do
  putStrLn "prop_unify_sound:"
  quickCheck prop_unify_sound
  putStrLn "prop_unify_self:"
  quickCheck prop_unify_self
  putStrLn "prop_idempotent:"
  quickCheck prop_idempotent