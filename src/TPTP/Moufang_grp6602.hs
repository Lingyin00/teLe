-- | Moufang loops
-- signature: mult/2, ld/2 (left division), rd/2 (right division)
module TPTP.Moufang_grp6602 where 

import Term
import LPO
import Rewrite
import Huet
import Pretty 

-- ================================================================

x, y, z :: Term
x = var "X"
y = var "Y"
z = var "Z"

mult, ld, rd :: Term -> Term -> Term
mult a b = app "mult" [a, b]
ld   a b = app "ld"   [a, b]
rd   a b = app "rd"   [a, b]

moufangAxioms :: [Equation]
moufangAxioms =
  [ Equation (mult x (ld x y)) y                          -- f01
  , Equation (ld x (mult x y)) y                          -- f02
  , Equation (mult (rd x y) y) x                          -- f03
  , Equation (rd (mult x y) y) x                          -- f04
  , Equation (mult (mult (mult x y) z) x) (mult x (mult y (mult z x)))  -- f05  Moufang
  ]

-- after conjecture and Skolem
a, b :: Term
a = app "sk_a" []
b = app "sk_b" []

moufangGoals :: [Equation]
moufangGoals =
  [ Equation (mult a (rd b b)) a
  , Equation (mult (rd b b) a) a
  ]

p6602 :: Prec
p6602 = precFromList ["ld", "rd", "mult", "sk_a", "sk_b"]
test6602 :: Maybe [MRule]
test6602 = huet p6602 moufangAxioms
result6602 :: IO ()
result6602 = putStrLn (pretty test6602)

-- =========================================================================
-- | result： FAILED ORIENT
--   mult(mult(B,C), A) = mult(A, mult(ld(A,B), mult(C,A)))
--
-- LPO cannot orient this in either direction. Both attempts compare a
-- variable against a non-variable term (A vs mult(B,C)), where LPO never
-- looks at the precedence. So no choice of precedence helps.
-- grp6603 has the same axioms, only changes the conjecture, 
-- so it cannot be solved by Huet completion as well.