{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Term
import Substitution
import Matching      (match)
import Unification   (unify)
import Rewrite
       ( Rule(..)
       , nonVarPos
       , freshVar, renameRule
       , rewriteAt, rewriteStep, normalize
       )
import LPO           (lpoNaive, Prec, precFGA)

import Control.Monad.State (evalState)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Test.QuickCheck

-- ============================================================
-- define a  precedence to do test "s >_lpo t"
-- ============================================================
testPrec :: Prec
testPrec = precFGA                    -- f > g > a > b

lpoGt :: Term -> Term -> Bool
lpoGt = lpoNaive testPrec             -- s >_lpo t

-- ============================================================
-- 0. Arbitrary instance
--    variabels {x,y,z}，function symbols {f,g,h}，constans {a,b}
-- ============================================================
instance Arbitrary Term where
  arbitrary = sized genTerm
    where
      genTerm :: Int -> Gen Term
      genTerm n
        | n <= 0    = oneof [genVar, genConst]
        | otherwise = oneof [genVar, genConst, genApp n]

      genVar   = VarT . Var <$> elements ["x", "y", "z"]
      genConst = (\c -> FunAppT (FuncSym c) []) <$> elements ["a", "b"]
      genApp n = do
        f  <- elements ["f", "g", "h"]
        k  <- choose (1, 2)
        ts <- vectorOf k (genTerm (n `div` 2))
        pure (FunAppT (FuncSym f) ts)

instance Arbitrary Rule where
  arbitrary = do
    l <- arbitrary `suchThat` isFunApp        -- lhs non-variable
    let lvars = Set.toList (vars l)
    r <- sized (genOver lvars)                -- Var(rhs) ⊆ Var(lhs)
    pure (Rule l r)
    where
      isFunApp (FunAppT _ _) = True
      isFunApp _             = False
      genConst = (\c -> FunAppT (FuncSym c) []) <$> elements ["a", "b"]
      genOver vs n
        | n <= 0 || null vs =
            oneof (genConst : [pure (VarT v) | v <- vs])
        | otherwise =
            oneof $
              [pure (VarT v) | v <- vs] ++
              [ genConst
              , do f  <- elements ["f", "g"]
                   k  <- choose (1, 2)
                   ts <- vectorOf k (genOver vs (n `div` 2))
                   pure (FunAppT (FuncSym f) ts)
              ]

varsRule :: Rule -> Set Var
varsRule (Rule l r) = vars l `Set.union` vars r

-- ============================================================
-- 1. Position round-trip
-- ============================================================
prop_replace_subterm_roundtrip :: Term -> Property
prop_replace_subterm_roundtrip t =
  forAll (elements (positions t)) $ \p ->
    case subtermAt t p of
      Just s  -> replaceAt t p s == Just t
      Nothing -> False

prop_subterm_after_replace :: Term -> Term -> Property
prop_subterm_after_replace t s =
  forAll (elements (positions t)) $ \p ->
    case replaceAt t p s of
      Just t' -> subtermAt t' p == Just s
      Nothing -> False

-- ============================================================
-- 2. nonVarPositions
-- ============================================================
notVarAt :: Term -> Pos -> Bool
notVarAt t p = case subtermAt t p of
  Just (VarT _) -> False
  Just _        -> True
  Nothing       -> False

prop_nonVarPos_correct :: Term -> Bool
prop_nonVarPos_correct t =
  all (notVarAt t) (nonVarPos t)
  && all (`elem` positions t) (nonVarPos t)

prop_nonVarPos_complete :: Term -> Bool
prop_nonVarPos_complete t =
  nonVarPos t == filter (notVarAt t) (positions t)

-- ============================================================
-- 3. renameRule
-- ============================================================
prop_rename_disjoint :: Rule -> Bool
prop_rename_disjoint r =
  let r' = evalState (renameRule r) 0
  in Set.null (varsRule r `Set.intersection` varsRule r')

prop_rename_structure :: Rule -> Bool
prop_rename_structure r =
  let Rule l  _ = r
      Rule l' _ = evalState (renameRule r) 0
  in positions l == positions l'

prop_rename_two_disjoint :: Rule -> Rule -> Bool
prop_rename_two_disjoint a b =
  let (a', b') =
        evalState (do x <- renameRule a
                      y <- renameRule b
                      pure (x, y)) 0
  in Set.null (varsRule a' `Set.intersection` varsRule b')

-- ============================================================
-- 4. rewrite under LPO （differential）
--    rules are oriented according to precFGA (f > g > a > b) 
-- ============================================================
orientedRules :: [Rule]
orientedRules =
  [ Rule (app "f" [app "g" [var "x"]]) (app "g" [var "x"])   -- f(g(x)) → g(x)
  , Rule (app "g" [app "g" [var "x"]]) (app "g" [var "x"])   -- g(g(x)) → g(x)
  , Rule (app "f" [ta'])              (app "g" [ta'])        -- f(a) → g(a)  (f>g)
  ]
  where ta' = app "a" []

-- every rule l >_lpo r（True）
prop_rules_oriented :: Bool
prop_rules_oriented = all (\(Rule l r) -> lpoGt l r) orientedRules

-- smaller after rewriting
prop_rewrite_decreases :: Term -> Bool
prop_rewrite_decreases t =
  case rewriteStep orientedRules t of
    Just t' -> lpoGt t t'
    Nothing -> True

-- normalize: the output is normal form（depending termination）
prop_normalize_is_nf :: Term -> Bool
prop_normalize_is_nf t =
  rewriteStep orientedRules (normalize orientedRules t) == Nothing

-- ============================================================
-- input
-- ============================================================
main :: IO ()
main = do
  putStrLn "== position round-trip =="
  quickCheck prop_replace_subterm_roundtrip
  quickCheck prop_subterm_after_replace
  putStrLn "== nonVarPositions =="
  quickCheck prop_nonVarPos_correct
  quickCheck prop_nonVarPos_complete
  putStrLn "== renameRule =="
  quickCheck prop_rename_disjoint
  quickCheck prop_rename_structure
  quickCheck prop_rename_two_disjoint
  putStrLn "== rewrite + LPO (differential) =="
  quickCheck prop_rules_oriented          -- must be satisfied first
  quickCheck prop_rewrite_decreases
  quickCheck prop_normalize_is_nf