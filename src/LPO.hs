module LPO where

import qualified Data.Set as Set
import Data.List (elemIndex)
import Term


-- Lexicographic Path Ordering
-- Optimization method : program transformation, implementation according to paper `THINGS TO KNOW WHEN IMPLEMENTING LPO`
-- TODO: implement the polynomial version from that paper.

-- precedence on function symbols
type Prec = FuncSym -> FuncSym -> Bool

-- a naive implementation for LPO: s ≻_lpo t  
lpoNaive :: Prec -> Term -> Term -> Bool
lpoNaive prec = gt where
    gt :: Term -> Term -> Bool
    gt s@(FunAppT f ss) t@(FunAppT g ts) =
        any (\si -> geq si t) ss -- rule alpa
        || ((prec f g) && all (gt s) ts) -- rule beta
        || (f == g && lexGT ss ts && all (gt s) ts) -- rule gamma
    gt s@(FunAppT _ _) (VarT v) = 
        Set.member v (vars s)
    gt (VarT _) _ = False
     
    -- lpo greater than or equal
    geq :: Term -> Term -> Bool
    geq t1 t2 = t1 == t2 || gt t1 t2
    
    -- compare lpo on subterm with index, these conditions must be satisfied:
    -- 1. index i, such that every 1..i-i, si = ti
    -- 2. gt si ti
    lexGT :: [Term] -> [Term] -> Bool
    lexGT [] [] = False
    lexGT (x : xs) (y : ys) 
        | x == y = lexGT xs ys
        | otherwise = gt x y
    lexGT _ _ = False

-- Test
precFromList :: [String] -> Prec
precFromList list (FuncSym x) (FuncSym y) =
    case (elemIndex x list, elemIndex y list) of
        (Just i, Just j) -> i < j 
        _ -> False

-- self-defined precedence
precFGA :: Prec
precFGA = precFromList ["f","g","a","b"]     -- f > g > a > b

precStar :: Prec
precStar = precFromList ["*","+","a","b"]     -- * > +  

precExp :: Prec
precExp = precFromList ["a","b","f","g"]      -- a > b > f > g  

-- self-defined terms
ta, tb :: Term
ta = app "a" []
tb = app "b" []

tx, ty, tz :: Term
tx = var "x"
ty = var "y"
tz = var "z"

-- f^n / g^n helper
fpow, gpow :: Int -> Term -> Term
fpow n base = iterate (\t -> app "f" [t]) base !! n
gpow n base = iterate (\t -> app "g" [t]) base !! n

-- every:(pattern, output, expected)
unitTests :: [(String, Bool, Bool)]
unitTests =
  [ ("f(a) > a (subterm)",        lpoNaive precFGA (app "f" [ta]) ta,          True)
  , ("f(x) > x (delta)",          lpoNaive precFGA (app "f" [tx]) tx,          True)
  , ("x not > f(x)",              lpoNaive precFGA tx (app "f" [tx]),          False)
  , ("f(a) not > f(a) (irrefl)",  lpoNaive precFGA (app "f" [ta]) (app "f" [ta]), False)
  , ("f(a) > g(a) (beta, f>g)",   lpoNaive precFGA (app "f" [ta]) (app "g" [ta]), True)
  , ("g(a) not > f(a)",           lpoNaive precFGA (app "g" [ta]) (app "f" [ta]), False)
  , ("f(f(a)) > f(a) (gamma)",    lpoNaive precFGA (app "f" [app "f" [ta]]) (app "f" [ta]), True)
  , ("x, y incomparable (1)",     lpoNaive precFGA tx ty,                      False)
  , ("x, y incomparable (2)",     lpoNaive precFGA ty tx,                      False)
  , ("distributivity orients",    lpoNaive precStar distLhs distRhs,           True)
  ]
  where
    distLhs = app "*" [tx, app "+" [ty, tz]]
    distRhs = app "+" [app "*" [tx, ty], app "*" [tx, tz]]

-- print PASS/FAIL
runUnitTests :: IO ()
runUnitTests = mapM_ check unitTests
  where
    check (name, got, want)
      | got == want = putStrLn ("PASS: " ++ name)
      | otherwise   = putStrLn ("FAIL: " ++ name
                                ++ "  (got " ++ show got
                                ++ ", expected " ++ show want ++ ")")

-- ghci :set +s
-- lpoNaive precExp (fpow 10 (app "b" [])) (gpow 10 (app "a" [])) -- False, (0.83 secs, 1,168,274,272 bytes)
-- lpoNaive precExp (fpow 12 (app "b" [])) (gpow 12 (app "a" [])) -- False, (11.98 secs, 17,223,473,304 bytes)
-- lpoNaive precExp (fpow 13 (app "b" [])) (gpow 13 (app "a" [])) -- False, (48.15 secs, 66,433,169,880 bytes)
-- lpoNaive precExp (gpow 13 (app "a" [])) (fpow 13 (app "b" [])) -- True (0.00 secs, 112,816 bytes)
-- lpoNaive precExp (fpow 14 (app "b" [])) (gpow 14 (app "a" [])) -- False (186.66 secs, 256,874,693,976 bytes)

-- n    | time (s) | ratio  | bytes (total allocation)
-- -----|----------|------- |----------
-- 10   | 0.83     | —      | 1.17 GB
-- 12   | 11.98    | * 14.4 | 17.2 GB
-- 13   | 48.15    | * 4.0  | 66.4 GB
-- 14   | 186.66   | * 3.9  | 256.9 GB