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

prettyCP :: CriticalPair -> String
prettyCP (CriticalPair l r _) = prettyTerm l ++ "  =?=  " ++ prettyTerm r

printCPs :: [CriticalPair] -> IO ()
printCPs = mapM_ (putStrLn . prettyCP)