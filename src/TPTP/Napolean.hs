module Napolean where

import Term
import Pretty
import LPO 
import Rewrite
import Huet
import CriticalPair


-- this file follows the tutorial "Monad Transformers Step by Step" by Martin Grabmüller

-- TPTP GRP777+1 : Napoleon's quasigroups
-- operation: product, difference (left division A\B), quotient (right division A/B)
--       bigC (arity with three), a/b/c (Skolem constant)

-- sos01: ∀B A. difference(A, product(A,B)) = B   —— A\(A·B) = B
sos01 :: Equation
sos01 = Equation
  (app "difference" [var "a_", app "product" [var "a_", var "b_"]])
  (var "b_")

-- sos02: ∀B A. product(A, difference(A,B)) = B   —— A·(A\B) = B
sos02 :: Equation
sos02 = Equation
  (app "product" [var "a_", app "difference" [var "a_", var "b_"]])
  (var "b_")

-- sos03: ∀B A. quotient(product(A,B), B) = A      —— (A·B)/B = A
sos03 :: Equation
sos03 = Equation
  (app "quotient" [app "product" [var "a_", var "b_"], var "b_"])
  (var "a_")

-- sos04: ∀B A. product(quotient(A,B), B) = A       —— (A/B)·B = A
sos04 :: Equation
sos04 = Equation
  (app "product" [app "quotient" [var "a_", var "b_"], var "b_"])
  (var "a_")

-- sos05: medial law  (A·B)·(C·D) = (A·C)·(B·D)
sos05 :: Equation
sos05 = Equation
  (app "product" [ app "product" [var "a_", var "b_"]
                 , app "product" [var "c_", var "d_"] ])
  (app "product" [ app "product" [var "a_", var "c_"]
                 , app "product" [var "b_", var "d_"] ])

-- sos06: idempotent  A·A = A
sos06 :: Equation
sos06 = Equation
  (app "product" [var "a_", var "a_"])
  (var "a_")

-- sos07: Napoleon  ((A·B)·B)·(B·(B·A)) = B
sos07 :: Equation
sos07 = Equation
  (app "product"
    [ app "product" [app "product" [var "a_", var "b_"], var "b_"]
    , app "product" [var "b_", app "product" [var "b_", var "a_"]] ])
  (var "b_")

-- sos08: bigC(A,B,C) = (A·B)·(C·A)
sos08 :: Equation
sos08 = Equation
  (app "bigC" [var "a_", var "b_", var "c_"])
  (app "product" [ app "product" [var "a_", var "b_"]
                 , app "product" [var "c_", var "a_"] ])

-- sos09: (a·c)·(c·b) = a·b
sos09 :: Equation
sos09 = Equation
  (app "product" [ app "product" [app "a" [], app "c" []]
                 , app "product" [app "c" [], app "b" []] ])
  (app "product" [app "a" [], app "b" []])

-- conjecture (goal): ∀X. bigC(a,b,X) = bigC(c,c,X)
goalNapoleon :: Equation
goalNapoleon = Equation
  (app "bigC" [app "a" [], app "b" [], var "x"])
  (app "bigC" [app "c" [], app "c" [], var "x"])

-- axiom set（
napoleonAxioms :: [Equation]
napoleonAxioms = [sos01, sos02, sos03, sos04, sos05, sos06, sos07, sos08, sos09]

goalNapoleonExpanded :: Equation
goalNapoleonExpanded = Equation
  -- bigC(a,b,X) = (a·b)·(X·a)
  (app "product" [ app "product" [app "a" [], app "b" []]
                 , app "product" [var "x", app "a" []] ])
  -- bigC(c,c,X) = (c·c)·(X·c)
  (app "product" [ app "product" [app "c" [], app "c" []]
                 , app "product" [var "x", app "c" []] ])

napoleonPrec = precFromList ["difference", "quotient", "product", "a", "b", "c"]
napoleonAxioms' = [sos01, sos02, sos03, sos04, sos05, sos06, sos07, sos09]  

-- result : nothing
-- FAILED ORIENT: product(product(a_,b_),product(c_,d_)) ≐ product(product(a_,c_),product(b_,d_))