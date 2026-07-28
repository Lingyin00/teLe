-- |
-- Module      : TPTP.Assoc_syn0831
-- Description : SYN083+1 (Pelletier 61) -- associativity implies the
--               four-variable generalised associativity law
--
-- signature: f/2
-- Variables follow the TPTP convention: upper case.
-- Classical completion succeeds here: the single axiom orients, the system
-- is convergent, and the goal joins. See note below.

module TPTP.Assoc_syn0831 where

import Term
import Pretty
import LPO 
import Rewrite
import Huet
import Decide

x, y, z, w :: Term
x = var "X"
y = var "Y"
z = var "Z"
w = var "W"

f :: Term -> Term -> Term
f s t = app "f" [s, t]

-- p61_1: f(X, f(Y,Z)) = f(f(X,Y), Z)
assoc0831 :: Equation
assoc0831 = Equation
  (f x (f y z))
  (f (f x y) z)

axioms0831 :: [Equation]
axioms0831 = [assoc0831]

-- pel61: f(X, f(Y, f(Z,W))) = f(f(f(X,Y), Z), W)
goal0831 :: Equation
goal0831 = Equation
  (f x (f y (f z w)))
  (f (f (f x y) z) w)

p0831 :: Prec
p0831 = precFromList ["f"]

test0831 :: Maybe [MRule]
test0831 = huet p0831 axioms0831
rules0831 :: IO ()
rules0831 = putStrLn (pretty test0831)
result0831 :: Maybe Bool
result0831 = decide p0831 axioms0831 goal0831

-- ================================================================
-- result：succeed.
-- LPO orients the axiom right-to-left, giving one rule:
--
--   f(f(X,Y),Z) -> f(X, f(Y,Z))
--
-- The only overlap is the rule with itself at position [0], and its critical
-- pair joins, so completion stops with a convergent one-rule system. Normal
-- forms are the right-nested terms.
--
-- The goal then joins: its left side is already normal, and the right side
-- reduces to it. The conjecture holds.