-- | Reproduction of the examples given in Knuth and Bendix,
-- /Simple Word Problems in Universal Algebras/ (1970).
--
-- Each example is run through 'huet' with a lexicographic path ordering. 
-- Note that the original paper uses a weight-based ordering rather than an LPO, 
-- so failure to orient an equation here does not necessarily correspond to a failure reported in the paper.

module ExamplesFromKnuth where

import Term
import LPO 
import Rewrite
import Huet
import Pretty
import System.CPUTime (getCPUTime)
import Control.Exception (evaluate)
import Text.Printf (printf)

-- ==== Summary===========================================================
--
-- @
-- #    Example                  Result       Expected     Knuth                    time
--------------------------------------------------------------------------------------
-- 1    Group theory             10 rules     10 rules     10 rules, 30 s          0.00s
-- 2    Group theory II          FAIL         FAIL         FAIL                    0.00s
-- 3    Group theory III         10 rules     10 rules     24 rules(8 redundant), 40 s    0.00s
-- 4    Inverse property         3 rules      3 rules      3 rules(per hand)       0.00s
-- 5    Group theory IV          12 rules     12 rules     12 rules, 50 s          0.00s
-- 6    Central groupoids I      3 rules      3 rules      3 rules(per hand)       0.00s
-- 7    Random axiom             FAIL         FAIL         FAIL(degenerate)        0.00s
-- 8    Random axiom II          FAIL         FAIL         FAIL (degenerate)       0.00s
-- 9A   Cancellation             2 rules      2 rules      2 rules                 0.00s
-- 9B   Cancellation + unit      8 rules      8 rules      8 rules                 0.00s
-- 10   Loops                    14 rules     14 rules     10 rules, 20s           0.00s
-- 11   Group theory V           12 rules     12 rules     12 rules, 2m15s         0.02s
-- 12   (l,r) systems I          9 rules      9 rules      10 rules, 110s          0.00s
-- 13   (r,l) systems            12 rules     12 rules     HALTED                  0.02s
-- 14   (l,r) systems II         12 rules     12 rules     21 rules, restart,2.5 min    0.00s
-- 15   (l,r) systems III        15 rules     15 rules     FAIL(degenerate)        0.04s
-- 16   Central groupoids II     FAIL         FAIL         13 rules, 9 min         0.00s
-- 17   Central groupoids III    5 rules      5 rules      25 rules, 2 min         0.00s
-- 18   Burnside groups          FAIL         FAIL         FAIL                    0.00s
--------------------------------------------------------------------------------------
-- @

-- ==== Three kinds of failure==========================================
--
-- The examples that do not complete fall into three distinct classes,
-- which is worth separating because only the third is addressed by
-- unfailing completion:
--
-- * /Variable condition violated./ Examples 7 and 8. The two sides of the
--   critical pair do not contain the same variables, so no rewrite rule
--   can be formed in either direction, independently of the ordering.
--   Example 8 is the extreme case: the equation is @z = y@, so the theory
--   collapses to a single element. Knuth resolves Example 7 by introducing
--   new operators.
--
-- * /Distinct variables compared./ Example 16. The two sides differ only
--   in one position, where they hold two distinct variables. No LPO can
--   orient this regardless of precedence, and no KBO can either.
--
-- * /Not orientable, variable condition satisfied./ Examples 11 (under one
--   precedence) and 18. Both sides have the same variables but are
--   incomparable. This is the case that ordered rewriting and unfailing
--   completion are designed for. Example 18 is where Knuth identifies the
--   commutative law as the major restriction of the method, and sketches
--   using two rules @a -> b@ and @b -> a@ together with a new notion of
--   irreducible form: this is, in outline, the unfailing completion later
--   developed by Bachmair, Dershowitz and Plaisted.
--
-- ==== The role of the precedence=======================================
--
-- Examples 12 to 15 all differ from the paper, and a single design
-- decision accounts for all four: the precedence used here places unary
-- operators above the binary operation, so nested unary symbols are
-- oriented towards the product and collapse.
--
-- * Example 12: @i(i(x)) -> f(x,e)@, the reverse of Knuth's orientation.
--   Two of his rules become derivable, giving 9 rules instead of 10.
-- * Example 13: the equation on which his procedure halted is never
--   generated, and the system converges.
-- * Example 14: the second inverse operator is eliminated outright by
--   @j(x) -> f(i(x),e2)@, giving 12 rules instead of 21.
-- * Example 15: the infinite family of nested unary terms that caused his
--   run to diverge never arises, and a finite canonical system exists.
--
-- Example 15 differs in kind rather than in degree: a set of axioms
-- reported as diverging turns out to admit a finite canonical system under
-- a different reduction ordering.
--
-- The strategy is not universal. Example 11 shows that the precedence is
-- decisive in both directions: of three precedences tried, one diverges,
-- one fails to orient, and one converges to the full group theory.
-- Example 16 shows its ceiling: there the obstruction is a comparison
-- between two variables, which no precedence controls.

-- ===============================================================
-- Example 1: group axioms with left identity and left inverse.
-- Completes to a canonical system of 10 rules.

-- | Precedence i > f > e, used for all group examples.
groupP :: Prec
groupP = precFromList ["i", "f", "e"]

-- | Left identity: e * x = x.
leftid :: Equation
leftid = Equation (app "f" [app "e" [], var "x"]) (var "x")

-- | Left inverse: i(x) * x = e.
leftinv :: Equation
leftinv = Equation (app "f" [app "i" [var "x"], var "x"]) (app "e" [])

-- | Associativity: (x * y) * z = x * (y * z).
associ :: Equation
associ = Equation (app "f" [app "f" [var "x", var "y"], var "z"])
                (app "f" [var "x", app "f" [var "y", var "z"]])  

-- | The three group axioms.
groupAxiom :: [Equation]
groupAxiom = [leftid, leftinv, associ]

-- | Result of completing 'groupAxiom' under 'groupP'
testGroup :: Maybe [MRule]
testGroup = huet groupP groupAxiom
result1 :: IO ()
result1 = putStrLn (pretty testGroup)

-- ========================================================================
-- Example 2: group theory II.
-- Result: FAILED ORIENT: f(_v332,i(_v334)) ≐ i(f(_v334,i(_v332)))
-- Same axioms as Example 1, but with precedence f > i instead of i > f.
-- Under KBO this corresponds to giving the inverse operator positive weight;
-- the only effect is that rule 20 is oriented in the opposite direction,
-- resulting in LPO is the change of precedence.

groupP2 :: Prec
groupP2 = precFromList ["f", "i", "e"]

testGroup2 :: Maybe [MRule]
testGroup2 = huet groupP2 groupAxiom
result2 :: IO ()
result2 = putStrLn (pretty testGroup2)

-- =========================================================================
-- Example 3: group theory III.
-- Right identity and right inverse instead of left.

-- | Right identity: x * e = x.
rightid :: Equation
rightid = Equation (app "f" [var "x", app "e" []]) (var "x")

-- | Right inverse: x * i(x) = e.
rightinv :: Equation
rightinv = Equation (app "f" [var "x", app "i" [var "x"]]) (app "e" [])

-- | Group axioms in right-sided form.
groupAxiomR :: [Equation]
groupAxiomR = [rightid, rightinv, associ]

testGroup3 :: Maybe [MRule]
testGroup3 = huet groupP groupAxiomR
result3 :: IO ()
result3 = putStrLn (pretty testGroup3)

-- ========================================================================
-- Example 4: inverse property.
-- A single axiom, no associativity and no identity.
-- Knuth reports that completion yields exactly three rules.

-- | Only the two operators f and i occur in this example.
invP :: Prec
invP = precFromList ["i", "f"]

-- | Inverse property: i(x) * (x * y) = y.
invProp :: Equation
invProp =
  Equation
    (app "f" [app "i" [var "x"], app "f" [var "x", var "y"]])
    (var "y")

testInvProp :: Maybe [MRule]
testInvProp = huet invP [invProp]
result4 :: IO ()
result4 = putStrLn (pretty testInvProp)

-- ========================================================================
-- Example 5: group theory IV.
-- Two left identities, each with its own left inverse.
-- Knuth's second identity is written f in the paper; here it is
-- renamed to e2, since f already denotes the binary operation.

-- | Precedence j > i > f > e2 > e.
groupP4 :: Prec
groupP4 = precFromList ["j", "i", "f", "e2", "e"]

-- | Second left identity: e2 * x = x.
leftid2 :: Equation
leftid2 = Equation (app "f" [app "e2" [], var "x"]) (var "x")

-- | Left inverse with respect to e2: j(x) * x = e2.
leftinv2 :: Equation
leftinv2 = Equation (app "f" [app "j" [var "x"], var "x"]) (app "e2" [])

-- | The five axioms of Example 5.
groupAxiom4 :: [Equation]
groupAxiom4 = [associ, leftid, leftid2, leftinv, leftinv2]

testGroup4 :: Maybe [MRule]
testGroup4 = huet groupP4 groupAxiom4
result5 :: IO ()
result5 = putStrLn (pretty testInvProp)

-- ===================================================================
-- Example 6: central groupoids I.
-- One binary operator and a single axiom, due to Evans.
-- Knuth reports that completion yields exactly three rules.

-- | Only the binary operator f occurs in this example.
cgP :: Prec
cgP = precFromList ["f"]

-- | Central groupoid axiom: (x * y) * (y * z) = y.
centralGroupoid :: Equation
centralGroupoid =
  Equation
    (app "f" [app "f" [var "x", var "y"], app "f" [var "y", var "z"]])
    (var "y")

testCentralGroupoid :: Maybe [MRule]
testCentralGroupoid = huet cgP [centralGroupoid]
result6 :: IO ()
result6 = putStrLn (pretty testCentralGroupoid)

-- ======================================================================
-- Example 7: a "random" axiom.
-- A single ternary operator. Completion fails: the first critical pair
-- yields an equation whose two sides contain different variables,
-- so it cannot be oriented under any reduction ordering.

-- | Only the ternary operator g occurs in this example.
randomP :: Prec
randomP = precFromList ["g"]

-- | g(x, g(y,z,x), w) = z.
randomAxiom :: Equation
randomAxiom =
  Equation
    (app "g" [var "x", app "g" [var "y", var "z", var "x"], var "w"])
    (var "z")

testRandom :: Maybe [MRule]
testRandom = huet randomP [randomAxiom]
result7 :: IO ()
result7 = putStrLn (pretty testRandom)

-- ========================================================================
-- Example 8: another "random" axiom.
-- Completion degenerates: the theory collapses to a single element.

-- | Only the binary operator f occurs in this example.
degenP :: Prec
degenP = precFromList ["f"]

-- | (x * y) * (z * (y * x)) = y.
degenAxiom :: Equation
degenAxiom =
  Equation
    (app "f"
      [ app "f" [var "x", var "y"]
      , app "f" [var "z", app "f" [var "y", var "x"]] ])
    (var "y")

testDegen :: Maybe [MRule]
testDegen = huet degenP [degenAxiom]
result8 :: IO ()
result8 = putStrLn (pretty testDegen)

-- =====================================================================
-- Example 9: cancellation laws.
-- Left and right cancellation are conditional axioms, not identities.
-- They are encoded by introducing two new binary operators lc and rc.

-- | Precedence lc > rc > f > e.
cancelP :: Prec
cancelP = precFromList ["lc", "rc", "f", "e"]

-- | Left cancellation: lc(x, x * y) = y.
leftCancel :: Equation
leftCancel =
  Equation (app "lc" [var "x", app "f" [var "x", var "y"]]) (var "y")

-- | Right cancellation: rc(x * y, y) = x.
rightCancel :: Equation
rightCancel =
  Equation (app "rc" [app "f" [var "x", var "y"], var "y"]) (var "x")

-- Part A: cancellation alone. Knuth reports these two are already complete.
testCancel :: Maybe [MRule]
testCancel = huet cancelP [leftCancel, rightCancel]
result9A :: IO ()
result9A = putStrLn (pretty testCancel)

-- Part B: with a unit element. Knuth reports four further rules.
testCancelUnit :: Maybe [MRule]
testCancelUnit = huet cancelP [leftCancel, rightCancel, leftid, rightid]
result9B :: IO ()
result9B = putStrLn (pretty testCancelUnit)

-- ==================================================================
-- Example 10: loops.
-- Two further binary operators for left and right division.
-- Knuth's \ and / are written ldiv and rdiv here.

-- | Precedence ldiv > rdiv > f.
loopP :: Prec
loopP = precFromList ["ldiv", "rdiv", "f"]

-- | x * (x \ y) = y.
loopLeft :: Equation
loopLeft =
  Equation (app "f" [var "x", app "ldiv" [var "x", var "y"]]) (var "y")

-- | (x / y) * y = x.
loopRight :: Equation
loopRight =
  Equation (app "f" [app "rdiv" [var "x", var "y"], var "y"]) (var "x")

testLoop :: Maybe [MRule]
testLoop = huet loopP [loopLeft, loopRight]
result10 :: IO ()
result10 = putStrLn (pretty testLoop)

-- part 10.2
loopPU :: Prec
loopPU = precFromList ["ldiv", "rdiv", "f", "e"]

testLoopUnit :: Maybe [MRule]
testLoopUnit = huet loopPU [loopLeft, loopRight, leftid, rightid]

-- part 10.3
loopPC :: Prec
loopPC = precFromList ["lc", "rc", "ldiv", "rdiv", "f", "e"]

testLoopFull :: Maybe [MRule]
testLoopFull =
  huet loopPC [loopLeft, loopRight, leftid, rightid, leftCancel, rightCancel]
result10f :: IO ()
result10f = putStrLn (pretty testLoopFull)
-- ======================================================================
-- Example 11: group theory V (Taussky).
-- Associativity, an idempotent e, at least one right inverse,
-- and at most one left inverse. The last is a conditional axiom (7.3),
-- encoded via a ternary operator t and a binary operator h,
-- following the same technique as Example 9.
-- This example is the most sensitive to the choice of precedence.
-- Three precedences were tried, with three qualitatively different
-- outcomes:
--
--   t > h > i > f > e   does not converge; |R| = 229 after 200 rounds,
--                       although every equation encountered was oriented
--                       successfully
--
--   t > h > f > i > e   fails to orient  f(x,e) = f(e,i(i(x))),
--                       which is (7.4) in the paper. Both sides have the
--                       same variables, so this is a genuine orientation
--                       failure rather than a violation of the variable
--                       condition
--
--   h > t > i > f > e   converges to 12 rules, ten of which are exactly
--                       the canonical system of Example 1. The auxiliary
--                       operators are eliminated: h reduces to t, and t
--                       retains only axiom 4
--
-- The third precedence reproduces Knuth's result, including the
-- consequence i(i(x)) -> x, which the paper reports as the 29th consequence derived.

-- | Precedence h > t > i > f > e.
tausskyP :: Prec
tausskyP = precFromList ["h", "t", "i", "f", "e"]

-- | Idempotent element: e * e = e.
idemE :: Equation
idemE = Equation (app "f" [app "e" [], app "e" []]) (app "e" [])

-- | Right inverse: x * i(x) = e.
rightinvE :: Equation
rightinvE = Equation (app "f" [var "x", app "i" [var "x"]]) (app "e" [])

-- | t(e, x, y) = x.
taussky4 :: Equation
taussky4 = Equation (app "t" [app "e" [], var "x", var "y"]) (var "x")

-- | t(x * y, x, y) = h(x * y, y).
taussky5 :: Equation
taussky5 =
  Equation
    (app "t" [app "f" [var "x", var "y"], var "x", var "y"])
    (app "h" [app "f" [var "x", var "y"], var "y"])

-- | The five axioms of Example 11.
tausskyAxioms :: [Equation]
tausskyAxioms = [associ, idemE, rightinvE, taussky4, taussky5]

testTaussky :: Maybe [MRule]
testTaussky = huet tausskyP tausskyAxioms
result11 :: IO ()
result11 = putStrLn (pretty testTaussky)

-- ===============================================================================
-- Example 12: (l, r) systems I, also known as left groups.
-- Left identity together with right inverse, in contrast to
-- Examples 1 (left/left) and 3 (right/right).
-- Knuth reports a complete set of ten reductions.

-- | Left identity and right inverse.
lrAxioms :: [Equation]
lrAxioms = [leftid, rightinv, associ]

testLR :: Maybe [MRule]
testLR = huet groupP lrAxioms
result12 :: IO ()
result12 = putStrLn (pretty testLR)

-- ==================================================================
-- Example 13: (r, l) systems.
-- Right identity with left inverse, dual to Example 12.
-- Knuth reports that his procedure stopped here on the equation
-- i(i(b)) * i(f(a,b)) = i(f(c,a)) * c, and that a new unary operator
-- had to be introduced to proceed.

-- My implementation converges to twelve rules without intervention.
-- The difference comes down to a single orientation: the LPO used here
-- has i > f, so i(i(x)) is oriented towards f(e,x) and double inverses
-- are eliminated eagerly. Knuth's weight-based ordering assigns weight
-- zero to the inverse operator, so a^-- is a normal form there and
-- survives into further overlaps. The equation on which his procedure
-- halted is therefore never generated here.
--
-- The resulting system is the exact mirror image of Example 12, so the
-- left-right asymmetry Knuth observed between the two does not appear
-- under the LPO.

-- | Right identity and left inverse.
rlAxioms :: [Equation]
rlAxioms = [rightid, leftinv, associ]

-- | Converges to twelve rules, where Knuth's procedure halted.
testRL :: Maybe [MRule]
testRL = huet groupP rlAxioms
result13 :: IO () 
result13 = putStrLn (pretty testRL)

-- ======================================================================
-- Example 14: (l, r) systems II.
-- Two left identities, each with its own right inverse.
-- Knuth's second identity f is renamed e2, and the second inverse
-- operator ~ is renamed j.

-- Knuth reports that after two minutes the computation was only slowly
-- approaching a complete set, with 35 axioms in the system, and was
-- terminated manually. He restarted with 19 initial axioms, obtained by
-- first completing the subsets {1,2,4} and {1,3,5} separately, and
-- reached a complete set of 21 reductions.
--
-- My implementation converges directly to twelve rules. Two differences
-- account for the smaller system:
--
--   The second inverse operator is eliminated outright by
--
--     j(x) -> f(i(x), e2)
--
--   whereas in Knuth's system j survives with its own rules
--   (a~~ -> a-~, a~- -> a--, and so on).
--
--   Double inverses are eliminated eagerly by i(i(x)) -> f(x,e), since
--   the LPO used here has i > f. Under Knuth's weight-based ordering the
--   inverse operator has weight zero, so a-- is a normal form and
--   survives into further overlaps. This single orientation also accounts
--   for the differences observed in Examples 12 and 13.
--
-- The two identities do not merge:
--
--     f(e2,x) -> x     e2 remains a left identity
--     i(e2)   -> e     only its inverse reduces to e
--
-- This contrasts sharply with Example 5, where left inverses force
-- e2 -> e and j(x) -> i(x), collapsing the two identities into one.
-- The contrast is a direct consequence of Example 12: an (l, r) system
-- is not a group, so uniqueness of the identity does not follow.

-- | Precedence j > i > f > e2 > e.
lr2P :: Prec
lr2P = precFromList ["j", "i", "f", "e2", "e"]

-- | Right inverse with respect to e2: x * j(x) = e2.
rightinv2 :: Equation
rightinv2 = Equation (app "f" [var "x", app "j" [var "x"]]) (app "e2" [])

-- | The five axioms of Example 14.
lr2Axioms :: [Equation]
lr2Axioms = [associ, leftid, leftid2, rightinv, rightinv2]

testLR2 :: Maybe [MRule]
testLR2 = huet lr2P lr2Axioms
result14 :: IO ()  
result14 = putStrLn (pretty testLR2)

-- ==================================================================
-- Example 15: (l, r) systems III, due to Clifford.
-- Associativity, a left identity, and two unary operators.
-- Knuth's ' and * are renamed p and s here.

-- Clifford proved that these axioms define exactly the (l, r) systems of
-- Example 12. Knuth reports that after two minutes the system was
-- diverging, with 32 axioms present, among them an evidently infinite
-- family of nested unary terms:
--
--     e'''''*  -> e''''''*      a*'''''  -> a*''''      a * a'''''  -> a''''''*
--
-- My implementation converges to fifteen rules. The infinite family never
-- arises, because nesting of the unary operators is eliminated as soon as
-- it appears:
--
--     f(p(p(x)), y) -> f(x, y)        double p collapses into the product
--     s(s(x))       -> s(x)           s is idempotent
--     s(p(x))       -> f(x, p(x))     mixed nesting is expanded into a product
--
-- The same mechanism is also observed in Examples 12, 13 and 14, where
-- i(i(x)) is oriented towards f(x,e). The LPO used here places the unary
-- operators above the binary operation, so nested unary symbols are always
-- oriented towards the product and collapse. Knuth's weight-based ordering
-- assigns weight zero to unary operators, so nested unary terms are normal
-- forms there and accumulate without bound.
--
-- Examples 12 to 14 differ from the paper in the size or shape of the
-- completed system. Example 15 differs in kind: a set of axioms reported
-- as diverging turns out to admit a finite canonical system under a
-- different reduction ordering.

-- | Precedence p > s > f > e.
cliffordP :: Prec
cliffordP = precFromList ["p", "s", "f", "e"]

-- | p(x) * x = s(x).
clifford3 :: Equation
clifford3 = Equation (app "f" [app "p" [var "x"], var "x"]) (app "s" [var "x"])

-- | s(x) * y = y.
clifford4 :: Equation
clifford4 = Equation (app "f" [app "s" [var "x"], var "y"]) (var "y")

-- | The four axioms of Example 15.
cliffordAxioms :: [Equation]
cliffordAxioms = [associ, leftid, clifford3, clifford4]

testClifford :: Maybe [MRule]
testClifford = huet cliffordP cliffordAxioms
result15 :: IO ()  
result15 = putStrLn (pretty testClifford)

-- =================================================================
-- Example 16: central groupoids II.
-- The central groupoid axiom of Example 6 extended by two unary operators
-- (subscripts 1 and 2 in the paper, renamed s1 and s2) and the weak axiom
-- s2(x) * y = x * y. Knuth reports 13 reductions after 9 minutes and calls
-- this the hardest problem his program solved.
--
-- Our implementation halts after six rounds on
--
--     f(y, f(y, x))  =  f(y, f(y, y))
--
-- which no LPO can orient: the sides differ only in one position, holding
-- the distinct variables x and y, and distinct variables are incomparable
-- under any precedence. Both s1 > s2 and s2 > s1 were tried.

-- | Precedence s1 > s2 > f.
cg2P :: Prec
cg2P = precFromList ["s2", "s1", "f"]

-- | (x * x) * x = s1(x).
cgSub1 :: Equation
cgSub1 =
  Equation
    (app "f" [app "f" [var "x", var "x"], var "x"])
    (app "s1" [var "x"])

-- | x * (x * x) = s2(x).
cgSub2 :: Equation
cgSub2 =
  Equation
    (app "f" [var "x", app "f" [var "x", var "x"]])
    (app "s2" [var "x"])

-- | s2(x) * y = x * y.
cgWeak :: Equation
cgWeak =
  Equation
    (app "f" [app "s2" [var "x"], var "y"])
    (app "f" [var "x", var "y"])

-- | The four axioms of Example 16.
cg2Axioms :: [Equation]
cg2Axioms = [cgSub1, cgSub2, centralGroupoid, cgWeak]

testCG2 :: Maybe [MRule]
testCG2 = huet cg2P cg2Axioms
result16 :: IO ()  
result16 = putStrLn (pretty testCG2)

-- ============================================================
-- Example 17:
-- result: succeed with returning 5 rules
-- | Axioms 1 to 3 of Example 16, without the weak axiom.
cg3Axioms :: [Equation]
cg3Axioms = [cgSub1, cgSub2, centralGroupoid]

testCG3 :: Maybe [MRule]
testCG3 = huet cg2P cg3Axioms
result17 :: IO ()  
result17 = putStrLn (pretty testCG3)

-- ===========================================================
-- Example 18:
-- commutativity, ensured to be failed
-- | Burnside group of exponent 3: x * (x * x) = e.
burnside :: Equation
burnside =
  Equation
    (app "f" [var "x", app "f" [var "x", var "x"]])
    (app "e" [])

burnsideAxioms :: [Equation]
burnsideAxioms = groupAxiom ++ [burnside]

testBurnside :: Maybe [MRule]
testBurnside = huet groupP burnsideAxioms
result18 :: IO ()  
result18 = putStrLn (pretty testBurnside)

-- =======================
-- outcome:
data Outcome = Rules Int | Fails
  deriving Eq

instance Show Outcome where
  show (Rules n) = show n ++ " rules"
  show Fails     = "FAIL"

data Example = Example
  { exNo       :: String
  , exName     :: String
  , exPrec     :: Prec
  , exAxioms   :: [Equation]
  , exExpected :: Outcome     -- expected
  , exKnuth    :: String      -- from Knuth
  }

examples :: [Example]
examples =
  [ Example "1"   "Group theory"          groupP     groupAxiom       (Rules 10) "10 rules, 30 s"
  , Example "2"   "Group theory II"       groupP2    groupAxiom       Fails  "FAIL"
  , Example "3"   "Group theory III"      groupP     groupAxiomR      (Rules 10) "24 rules(8 redundant), 40 s"
  , Example "4"   "Inverse property"      invP       [invProp]        (Rules 3)  "3 rules(per hand)"
  , Example "5"   "Group theory IV"       groupP4    groupAxiom4      (Rules 12) "12 rules, 50 s"
  , Example "6"   "Central groupoids I"   cgP        [centralGroupoid](Rules 3)  "3 rules(per hand)"
  , Example "7"   "Random axiom"          randomP    [randomAxiom]    Fails      "FAIL(degenerate)"
  , Example "8"   "Random axiom II"       degenP     [degenAxiom]     Fails      "FAIL (degenerate)"
  , Example "9A"  "Cancellation"          cancelP    [leftCancel, rightCancel]        (Rules 2) "2 rules"
  , Example "9B"  "Cancellation + unit"   cancelP    [leftCancel, rightCancel, leftid, rightid] (Rules 8) "8 rules"
  , Example "10"  "Loops"                 loopPC      [loopLeft, loopRight, leftid, rightid, leftCancel, rightCancel]  (Rules 14)  "10 rules, 20s"
  , Example "11"  "Group theory V"        tausskyP   tausskyAxioms    (Rules 12) "12 rules, 2m15s"
  , Example "12"  "(l,r) systems I"       groupP     lrAxioms         (Rules 9)  "10 rules, 110s"
  , Example "13"  "(r,l) systems"         groupP     rlAxioms         (Rules 12) "HALTED"
  , Example "14"  "(l,r) systems II"      lr2P       lr2Axioms        (Rules 12) "21 rules, restart,2.5 min"
  , Example "15"  "(l,r) systems III"     cliffordP  cliffordAxioms   (Rules 15) "FAIL(degenerate)"
  , Example "16"  "Central groupoids II"  cg2P       cg2Axioms        Fails      "13 rules, 9 min"
  , Example "17"  "Central groupoids III" cg2P       cg3Axioms        (Rules 5) "25 rules, 2 min"
  , Example "18"  "Burnside groups"       groupP     burnsideAxioms   Fails      "FAIL"
  ]

runExample :: Example -> IO (Outcome, Double)
runExample ex = do
  t0 <- getCPUTime
  let out = case huet (exPrec ex) (exAxioms ex) of
              Nothing -> Fails
              Just rs -> Rules (length rs)
  _  <- evaluate (case out of Rules n -> n; Fails -> 0)
  t1 <- getCPUTime
  pure (out, fromIntegral (t1 - t0) / 1e12)

runAll :: IO Bool
runAll = do
  printf "%-4s %-24s %-12s %-12s %-20s %8s\n"
         "#" "Example" "Result" "Expected" "Knuth" "time"
  putStrLn (replicate 86 '-')
  oks <- mapM row examples
  putStrLn (replicate 86 '-')
  let n = length (filter not oks)
  printf "%d/%d matched\n" (length examples - n) (length examples)
  pure (n == 0)
  where
    row ex = do
      (got, secs) <- runExample ex
      let ok = got == exExpected ex
      printf "%-4s %-24s %-12s %-12s %-20s %7.2fs%s\n"
             (exNo ex) (exName ex) (show got) (show (exExpected ex))
             (exKnuth ex) secs (if ok then "" else "   <-- MISMATCH")
      pure ok