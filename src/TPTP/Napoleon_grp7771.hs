-- |
-- Description : Napoleon quasigroups -- bigC(a,b,X) = bigC(c,c,X)
--
-- signature: product/2, difference/2 (left division A\B),
--            quotient/2 (right division A/B), bigC/3,
--            a/0, b/0, c/0 (problem constants)

-- Classical completion fails here on the medial law (sos05); see note below.
module TPTP.Napoleon_grp7771 where

import Term
import Rewrite
import LPO 
import Huet
import Pretty

-- variables (v prefix) and constants (c prefix)
vA, vB, vC, vD, vX :: Term
vA = var "A"
vB = var "B"
vC = var "C"
vD = var "D"
vX = var "X"

cA, cB, cC :: Term
cA = app "a" []
cB = app "b" []
cC = app "c" []

-- 'product' and 'quot' are taken by Prelude, hence prod / ldiv / rdiv
prod, ldiv, rdiv :: Term -> Term -> Term
prod s t = app "product"    [s, t]
ldiv s t = app "difference" [s, t]
rdiv s t = app "quotient"   [s, t]

bigC :: Term -> Term -> Term -> Term
bigC s t u = app "bigC" [s, t, u]

-- sos01: A \ (A · B) = B
sos01 :: Equation
sos01 = Equation (ldiv vA (prod vA vB)) vB

-- sos02: A · (A \ B) = B
sos02 :: Equation
sos02 = Equation (prod vA (ldiv vA vB)) vB

-- sos03: (A · B) / B = A
sos03 :: Equation
sos03 = Equation (rdiv (prod vA vB) vB) vA

-- sos04: (A / B) · B = A
sos04 :: Equation
sos04 = Equation (prod (rdiv vA vB) vB) vA

-- sos05: medial law  (A·B)·(C·D) = (A·C)·(B·D)
sos05 :: Equation
sos05 = Equation
  (prod (prod vA vB) (prod vC vD))
  (prod (prod vA vC) (prod vB vD))

-- sos06: idempotence  A · A = A
sos06 :: Equation
sos06 = Equation (prod vA vA) vA

-- sos07: Napoleon  ((A·B)·B) · (B·(B·A)) = B
sos07 :: Equation
sos07 = Equation
  (prod (prod (prod vA vB) vB)
        (prod vB (prod vB vA)))
  vB

-- sos08: definition of bigC  bigC(A,B,C) = (A·B)·(C·A)
sos08 :: Equation
sos08 = Equation
  (bigC vA vB vC)
  (prod (prod vA vB) (prod vC vA))

-- sos09: (a·c) · (c·b) = a·b
sos09 :: Equation
sos09 = Equation
  (prod (prod cA cC) (prod cC cB))
  (prod cA cB)

axioms :: [Equation]
axioms = [sos01, sos02, sos03, sos04, sos05, sos06, sos07, sos08, sos09]

-- bigC eliminated by hand, for use with goalExpanded
axiomsWithoutBigC :: [Equation]
axiomsWithoutBigC = [sos01, sos02, sos03, sos04, sos05, sos06, sos07, sos09]

-- conjecture: bigC(a,b,X) = bigC(c,c,X)
goal :: Equation
goal = Equation (bigC cA cB vX) (bigC cC cC vX)

-- same goal with sos08 unfolded by hand: (a·b)·(X·a) = (c·c)·(X·c)
goalExpanded :: Equation
goalExpanded = Equation
  (prod (prod cA cB) (prod vX cA))
  (prod (prod cC cC) (prod vX cC))

p7771 :: Prec
p7771 =
  precFromList ["bigC", "difference", "quotient", "product", "a", "b", "c"]

test7771 :: Maybe [MRule]
test7771 = huet p7771 axiomsWithoutBigC
result7771 :: IO ()
result7771 = putStrLn (pretty test7771)

-- ===========================================================================
-- | result: Failed orient:
--   product(product(A,B), product(C,D)) = product(product(A,C), product(B,D))
--
-- The right-hand side is the left-hand side with B and C swapped, so the
-- equation is permutative.  this is the same kind of failure as commutativity.
