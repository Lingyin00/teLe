-- |
-- Module      : TPTP.Inverse_grp77001
-- Description : Moufang loops with unit -- every element has a two-sided
--               inverse
--
-- signature: mult/2, ld/2 (left division), rd/2 (right division), unit/0
-- f07 and f08 are Moufang identities.
-- Variables follow the TPTP convention: upper case.
--
-- NOTE: the conjecture is ∀X0 ∃X1 (...), which after negation is a clause
-- with two negative literals -- outside unit equational logic, so neither
-- classical nor unfailing completion can take it directly. The existential
-- is discharged by hand here: in a loop the inverse is definable, and
-- ld(X0, unit) is a left inverse of X0. Substituting that witness turns the
-- conjecture into two ordinary equational goals. This substitution is a
-- manual step, not something the implementation derives.

-- result：failed orient. see below.
module TPTP.Inverse_grp77001 where

import Term
import LPO 
import Rewrite
import Huet

x, y, z :: Term
x = var "X"
y = var "Y"
z = var "Z"

unit :: Term
unit = app "unit" []

mult, ld, rd :: Term -> Term -> Term
mult s t = app "mult" [s, t]
ld   s t = app "ld"   [s, t]
rd   s t = app "rd"   [s, t]

axioms77001 :: [Equation]
axioms77001 =
  -- f01: A · (A \ B) = B
  [ Equation (mult x (ld x y)) y
  -- f02: A \ (A · B) = B
  , Equation (ld x (mult x y)) y
  -- f03: (A / B) · B = A
  , Equation (mult (rd x y) y) x
  -- f04: (A · B) / B = A
  , Equation (rd (mult x y) y) x
  -- f05: A · unit = A
  , Equation (mult x unit) x
  -- f06: unit · A = A
  , Equation (mult unit x) x
  -- f07: ((A·B)·A) · (A·C) = A · (((B·A)·A)·C)
  , Equation
      (mult (mult (mult x y) x) (mult x z))
      (mult x (mult (mult (mult y x) x) z))
  -- f08: (A·B) · (B·(C·B)) = (A·(B·(B·C))) · B
  , Equation
      (mult (mult x y) (mult y (mult z y)))
      (mult (mult x (mult y (mult y z))) y)
  ]

-- Skolem constant for X0
skA :: Term
skA = app "sk_a" []

-- witness for X1, supplied by hand: the left inverse of X0
inv :: Term
inv = ld skA unit

goals77001 :: [Equation]
goals77001 =
  -- X1 · X0 = unit, i.e. (a \ unit) · a = unit   -- the real content
  [ Equation (mult inv skA) unit
  -- X0 · X1 = unit, i.e. a · (a \ unit) = unit   -- an instance of f01
  , Equation (mult skA inv) unit
  ]

p77001 :: Prec
p77001 = precFromList ["ld", "rd", "mult", "unit", "sk_a"]

test77001 :: Maybe [MRule]
test77001 = huet p77001 axioms77001

-- =========================================================================
-- | result : FAILED ORIENT: 
-- mult(mult(mult(X,Y),X),mult(X,Z)) ≐ mult(X,mult(mult(mult(Y,X),X),Z))
-- this is not the permutation case, but LPO still fails.
-- TODO: add analysis here.