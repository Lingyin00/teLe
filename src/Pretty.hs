module Pretty where

import Data.List (intercalate)
import Term
import Rewrite
import CriticalPair

prettyTerm :: Term -> String
prettyTerm (VarT (Var x)) = x
prettyTerm (FunAppT (FuncSym f) []) = f
prettyTerm (FunAppT (FuncSym f) ts) = f ++ "(" ++ intercalate "," (map prettyTerm ts) ++ ")"

prettyRule :: Rule -> String
prettyRule (Rule l r) = prettyTerm l ++ "->" ++ prettyTerm r

prettyMaybeRule :: Maybe Rule -> String
prettyMaybeRule Nothing  = "<unorientable>"
prettyMaybeRule (Just r) = prettyRule r

prettyCP :: CriticalPair -> String
prettyCP (CriticalPair l r _) = prettyTerm l ++ "  =?=  " ++ prettyTerm r

prettyEquation :: Equation -> String
prettyEquation (Equation s t) = prettyTerm s ++ " ≐ " ++ prettyTerm t

printCPs :: [CriticalPair] -> IO ()
printCPs = mapM_ (putStrLn . prettyCP)

printMaybeRule :: Maybe Rule -> IO ()
printMaybeRule = putStrLn . prettyMaybeRule


-- define my own pretty print class as unified interface!
class Pretty a where
  pretty :: a -> String

instance Pretty Term where pretty = prettyTerm
instance Pretty Rule where pretty = prettyRule
instance Pretty Equation where pretty = prettyEquation
instance Pretty a => Pretty (Maybe a) where
  pretty Nothing  = "<none>"
  pretty (Just x) = pretty x
instance Pretty a => Pretty [a] where
  pretty xs = unlines (map pretty xs)