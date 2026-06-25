module Huet where

-- Implementation of the `Huet´s completion procedure` according to `TRaAT` written by Nipkow & Baader
-- Input: Set E of identities, Terminating set R of rewrite rules
-- rules may be marked or not(for computing critical pairs)
import Term
import Rewrite
import LPO
import CriticalPair
import Pretty
import Debug.Trace (trace)
import Data.List (sortOn)

prettyMRule :: MRule -> String
prettyMRule (MRule r m) =
  pretty r ++ "    [" ++ if m then "marked]" else "unmarked" ++ "]"

instance Pretty MRule where
  pretty = prettyMRule

-- orient an equation by using term ordering
orient :: Prec -> Equation -> Maybe Rule
orient gt (Equation left right) 
    | lpoNaive gt left right = Just (Rule left right)
    | lpoNaive gt right left = Just (Rule right left)
    | otherwise = Nothing -- this is the difference between classical kbc and unfailing kbc
-- test orient
precSelf = precFromList["f", "g"]
test1 = orient precSelf (Equation (app "f" [app "a" []]) (app "a" []))
test2 = orient precSelf (Equation (var "x") (var "y"))
test3 = orient precSelf (Equation (app "g" [app "a" []]) (app "f" [app "a" []]))

-- make an equation from critical pair
mkEqFromCp :: CriticalPair -> Equation
mkEqFromCp cp = Equation (cpl cp) (cpr cp)

mkEqsFromCps :: [CriticalPair] -> [Equation]
mkEqsFromCps = map mkEqFromCp

-- helper funciton for term size
termSize :: Term -> Int
termSize (VarT _) = 1
termSize (FunAppT _ args) = 1 + sum (map termSize args)

eqSize :: Equation -> Int
eqSize (Equation l r) = termSize l + termSize r

sortEqs :: [Equation] -> [Equation]
sortEqs = sortOn eqSize

-- fairness : rules with marker
data MRule = MRule{
    mrule :: Rule,
    marked :: Bool} deriving (Show)

-- Begins here: the Huet's completion loop
allMarked :: [MRule] -> Bool
allMarked = all marked

-- find if there's an unmarked rule in rule list
findUnmarked :: [MRule] -> Maybe (MRule, [MRule])
findUnmarked rls =
    case span marked rls of -- break (not . marked) == span marked (cut the list at the first unmarked position)
        (before, x : after) -> Just (x, before ++ after)
        (_, []) -> Nothing -- going through all elements in the list and we didn't find this kind of unmarked rule

markRule :: MRule -> MRule
markRule a = a {marked = True}

-- Rule deduce
deduce :: MRule -> [MRule] -> Fresh [Equation]
deduce r mrs = do
    let self = mrule r
        markedRule = map mrule (filter marked mrs)
    selfCP <- criticalPairs self self
    otherCPs <- mapM (biDirectionCP self) markedRule
    pure (map mkEqFromCp (selfCP ++ concat otherCPs))
    where
        biDirectionCP a b = do
            c1 <- criticalPairs a b
            c2 <- criticalPairs b a
            pure (c1 ++ c2)

-- helper: whether newRule could rewrite a rule at some position
reduceByRule :: Rule -> Term -> Maybe Term
reduceByRule newRule rule =
    case [g' | pos <- positions rule, Just g' <- [rewriteAt newRule pos rule]] of
        [] -> Nothing
        (g' : _) -> Just g'

-- TODO helper: divide the rls into rules which can be reduced by newRule and which can not
composeCollapse :: [Rule] -> Rule -> [MRule] -> ([MRule], [Equation])
composeCollapse allRules newRule = foldr classify ([], [])
  where
    classify mr (keptAcc, eqAcc) =
      let g = lhs (mrule mr)   -- lhs of the current rule
          d = rhs (mrule mr)   -- rhs of the current rule
      in case reduceByRule newRule g of
           -- Collapse
           Just g' -> (keptAcc, Equation g' d : eqAcc)
           -- Compose
           Nothing ->
             let d' = normalize allRules d
             in (mr { mrule = Rule g d' } : keptAcc, eqAcc)


huet :: Prec -> [Equation] -> Maybe [MRule]
huet p es = runFresh(outer 0 (sortEqs es) [])
  where -- es = E_0, [] = R_0
    -- TODO: Is preprocessing needed here??
    outer :: Int -> [Equation] -> [MRule] -> Fresh(Maybe [MRule])
    outer n eqs rls 
      | n > 100    = trace ("STOP at " ++ show n) $ pure (Just rls)
      | null eqs && allMarked rls = pure(Just rls)
      | otherwise = trace ("outer " ++ show n ++ ": |E|=" ++ show (length eqs) ++ " |R|=" ++ show (length rls) ++ " marked=" ++ show (length (filter marked rls))) $ do-- enter into the inner loop
        res <- inner eqs rls
        case res of
            Nothing -> pure Nothing -- completion fails
            Just r' -> case findUnmarked r' of -- E is empty right now
                            Nothing -> pure (Just r') 
                            -- using umRule to compute its critical pair with itself or other marked rule
                            -- deduce this critical pair to equation, add this equation to E
                            -- mark umRule
                            -- enter into inner loop again
                            Just (umRule, r'') -> do -- rule f)
                                newEqs <- deduce umRule r''
                                let newRls = markRule umRule : r''
                                outer (n+1) (sortEqs newEqs) newRls
    inner :: [Equation] -> [MRule] -> Fresh(Maybe [MRule]) -- step from a to e
    inner [] rls = pure (Just rls)
    inner (eq : eqs) rls = do
        -- take one equation, which is eq here, normalize its lhs and its rhs
        let rls' = map mrule rls -- rule a) b)
            normal_lhs = normalize rls' (eql eq)
            normal_rhs = normalize rls' (eqr eq)
        if normal_lhs == normal_rhs then inner eqs rls
           else case orient p (Equation normal_lhs normal_rhs) of
                    Nothing -> trace ("FAILED ORIENT: " ++ pretty (Equation normal_lhs normal_rhs)) $
                        pure Nothing -- rule d)
                    Just newRule -> 
                        trace ("ORIENT: " ++ pretty newRule) $
                        let allRules = newRule : rls'
                            (keptMRs, collapsedEqs) = composeCollapse allRules newRule rls
                            newMR = MRule newRule False
                        in inner (sortEqs (collapsedEqs ++ eqs)) (newMR : keptMRs)

                    -- filter out rules in R which cannot been reduced by newRule
                    -- keep the lhs of those rules and normalize rhs by R ∪ {newRule}, inherit marker
                    -- newRule is unmarked
                    -- add newRule to this new rule set
                    -- remove eq from the original equation set
                    -- add new equations to the equation set: new equations are from those reduced rules(keep the reduced lhs and keep rhs unchanged)

-- huet with postpone
huetP :: Prec -> [Equation] -> Maybe [MRule]
huetP p es = runFresh (outer 0 (sortEqs es) [])
  where
    maxOuter :: Int
    maxOuter = 100

    maxPostpone :: Int
    maxPostpone = 200

    maxRules :: Int
    maxRules = 500

    maxEqs :: Int
    maxEqs = 1000

    outer :: Int -> [Equation] -> [MRule] -> Fresh (Maybe [MRule])
    outer n eqs rls
      | n > maxOuter =
          trace ("STOP: max outer reached at " ++ show n) $
          pure Nothing
      | length rls > maxRules =
          trace ("STOP: too many rules: " ++ show (length rls)) $
          pure Nothing
      | length eqs > maxEqs =
          trace ("STOP: too many equations: " ++ show (length eqs)) $
          pure Nothing
      | null eqs && allMarked rls =
          pure (Just rls)
      | otherwise =
          trace ("outer " ++ show n
            ++ ": |E|=" ++ show (length eqs)
            ++ " |R|=" ++ show (length rls)
            ++ " marked=" ++ show (length (filter marked rls))) $ do
            res <- inner maxPostpone (sortEqs eqs) rls
            case res of
              Nothing -> pure Nothing
              Just r' ->
                case findUnmarked r' of
                  Nothing -> pure (Just r')
                  Just (umRule, r'') -> do
                    newEqs <- deduce umRule r''
                    let newRls = markRule umRule : r''
                    outer (n + 1) (sortEqs newEqs) newRls

    inner :: Int -> [Equation] -> [MRule] -> Fresh (Maybe [MRule])
    inner _ [] rls = pure (Just rls)
    inner postponeLeft (eq : eqs) rls = do
      let rls' = map mrule rls
          normal_lhs = normalize rls' (eql eq)
          normal_rhs = normalize rls' (eqr eq)
          normalizedEq = Equation normal_lhs normal_rhs

      if normal_lhs == normal_rhs
        then inner postponeLeft eqs rls
        else case orient p normalizedEq of
          Nothing ->
            if postponeLeft <= 0
              then
                trace ("FAILED ORIENT after postponing: "
                  ++ show normal_lhs ++ "  =?=  " ++ show normal_rhs) $
                pure Nothing
              else
                trace ("POSTPONE: "
                  ++ show normal_lhs ++ "  =?=  " ++ show normal_rhs) $
                inner (postponeLeft - 1) (sortEqs (eqs ++ [normalizedEq])) rls

          Just newRule ->
            trace ("ORIENT: "
              ++ show (lhs newRule) ++ "  ->  " ++ show (rhs newRule)) $
            let allRules = newRule : rls'
                (keptMRs, collapsedEqs) = composeCollapse allRules newRule rls
                newMR = MRule newRule False
            in inner maxPostpone
                 (sortEqs (collapsedEqs ++ eqs))
                 (newMR : keptMRs)


-- test with group axioms
groupPrec :: Prec
groupPrec = precFromList ["i", "f", "e"]

ax1, ax2, ax3 :: Equation
ax1 = Equation (app "f" [app "e" [], var "x"]) (var "x")
ax2 = Equation (app "f" [app "i" [var "x"], var "x"]) (app "e" [])
ax3 = Equation (app "f" [app "f" [var "x", var "y"], var "z"])          -- f(f(x,y),z)
                (app "f" [var "x", app "f" [var "y", var "z"]])         -- f(x,f(y,z))

-- not convergent in 10 minutes...
groupAxioms :: [Equation]
groupAxioms = [ax1, ax2, ax3]

runGroup :: Maybe [MRule]
runGroup = huet groupPrec groupAxioms

-- following are some tests for components
-- 1.
simplePrec :: Prec
simplePrec = precFromList ["f", "a"]

simpleEqs :: [Equation]
simpleEqs = [ Equation (app "f" [var "x"]) (var "x") ]

runSimple :: Maybe [MRule]
runSimple = huet simplePrec simpleEqs

-- 2.
cpPrec :: Prec
cpPrec = precFromList ["f", "g", "h", "a", "b"]

cpEqs :: [Equation]
cpEqs =
  [ Equation (app "f" [app "g" [var "x"]]) (app "h" [var "x"])
  , Equation (app "g" [app "a" []]) (app "b" [])
  ]

runCP :: Maybe [MRule]
runCP = huet cpPrec cpEqs

-- 3.
collapsePrec :: Prec
collapsePrec = precFromList ["f", "a", "b", "c"]

collapseEqs :: [Equation]
collapseEqs =
  [ Equation (app "f" [app "a" []]) (app "b" [])
  , Equation (app "a" []) (app "c" [])
  ]

runCollapse :: Maybe [MRule]
runCollapse = huet collapsePrec collapseEqs

-- 4.
varPrec :: Prec
varPrec = precFromList ["f"]

varEqs :: [Equation]
varEqs = [ Equation (var "x") (var "y") ]

runVar :: Maybe [MRule]
runVar = huet varPrec varEqs

cancelAx :: Equation
cancelAx =
  Equation
    (app "f" [app "i" [var "x"], app "f" [var "x", var "y"]])
    (var "y")
groupAxiomsWithCancel :: [Equation]
groupAxiomsWithCancel = [ax1, ax2, ax3, cancelAx]

runGroupWithCancel :: Maybe [MRule]
runGroupWithCancel = huet groupPrec groupAxiomsWithCancel

invMulAx :: Equation
invMulAx =
  Equation
    (app "i" [app "f" [var "x", var "y"]])
    (app "f" [app "i" [var "y"], app "i" [var "x"]])

groupAxiomsWithCancelInvMul :: [Equation]
groupAxiomsWithCancelInvMul =
  [ax1, ax2, ax3, cancelAx, invMulAx]

runGroupWithCancelInvMul :: Maybe [MRule]
runGroupWithCancelInvMul =
  huet groupPrec groupAxiomsWithCancelInvMul

rightIdAx :: Equation
rightIdAx =
  Equation
    (app "f" [var "x", app "e" []])
    (var "x")

doubleInvAx :: Equation
doubleInvAx =
  Equation
    (app "i" [app "i" [var "x"]])
    (var "x")

rightInvAx :: Equation
rightInvAx =
  Equation
    (app "f" [var "x", app "i" [var "x"]])
    (app "e" [])

friendlyGroupAxioms :: [Equation]
friendlyGroupAxioms =
  [ ax1
  , rightIdAx
  , ax2
  , rightInvAx
  , ax3
  , cancelAx
  , invMulAx
  , doubleInvAx
  ]

runFriendlyGroup :: Maybe [MRule]
runFriendlyGroup = huet groupPrec friendlyGroupAxioms
-- putStrLn (pretty runFriendlyGroup)

-- test with Monoid
monoidPrec :: Prec
monoidPrec = precFromList ["f", "e"]

monoidAx1, monoidAx2, monoidAx3 :: Equation
monoidAx1 =
  Equation
    (app "f" [app "e" [], var "x"])
    (var "x")

monoidAx2 =
  Equation
    (app "f" [var "x", app "e" []])
    (var "x")

monoidAx3 =
  Equation
    (app "f" [app "f" [var "x", var "y"], var "z"])
    (app "f" [var "x", app "f" [var "y", var "z"]])

monoidAxioms :: [Equation]
monoidAxioms = [monoidAx1, monoidAx2, monoidAx3]

runMonoid :: Maybe [MRule]
runMonoid = huet monoidPrec monoidAxioms
--putStrLn (pretty runMonoid)

-- another try with group axioms
-- result: failed because of e * x -> x
rightGroupAx1 :: Equation
rightGroupAx1 =
  Equation
    (app "f" [var "x", app "e" []])
    (var "x")

rightGroupAx2 :: Equation
rightGroupAx2 =
  Equation
    (app "f" [var "x", app "i" [var "x"]])
    (app "e" [])

rightGroupAx3 :: Equation
rightGroupAx3 =
  Equation
    (app "f" [app "f" [var "x", var "y"], var "z"])
    (app "f" [var "x", app "f" [var "y", var "z"]])

rightGroupAxioms :: [Equation]
rightGroupAxioms =
  [ rightGroupAx1
  , rightGroupAx2
  , rightGroupAx3
  ]

runRightGroup :: Maybe [MRule]
runRightGroup = huet groupPrec rightGroupAxioms

-- plus test （still failed because lack of i(x * y) -> i(y) * i(x) and x * (i(x) * y) -> y).
leftIdAx :: Equation
leftIdAx =
  Equation
    (app "f" [app "e" [], var "x"])
    (var "x")

rightGroupPlusLeftId :: [Equation]
rightGroupPlusLeftId =
  [ rightGroupAx1
  , rightGroupAx2
  , rightGroupAx3
  , leftIdAx
  ]


-- failed because of
-- a * (i(x * (y * a)) * z) = b * (i(x * (y * b)) * z)
runRightGroupPlusLeftId :: Maybe [MRule]
runRightGroupPlusLeftId = huetP groupPrec rightGroupPlusLeftId

-- exponential
idemMonoidPrec :: Prec
idemMonoidPrec = precFromList ["f", "e"]

idemAx :: Equation
idemAx =
  Equation
    (app "f" [var "x", var "x"])
    (var "x")

idemMonoidAxioms :: [Equation]
idemMonoidAxioms =
  [ monoidAx1
  , monoidAx2
  , monoidAx3
  , idemAx
  ]

runIdemMonoid :: Maybe [MRule]
runIdemMonoid = huetP idemMonoidPrec idemMonoidAxioms

-- exponential
bandPrec :: Prec
bandPrec = precFromList ["f"]

bandAxioms :: [Equation]
bandAxioms =
  [ monoidAx3
  , idemAx
  ]

runBand :: Maybe [MRule]
runBand = huet bandPrec bandAxioms

-- succeed
natPlusPrec :: Prec
natPlusPrec = precFromList ["plus", "s", "zero"]

natPlusAxioms :: [Equation]
natPlusAxioms =
  [ Equation
      (app "plus" [app "zero" [], var "y"])
      (var "y")
  , Equation
      (app "plus" [app "s" [var "x"], var "y"])
      (app "s" [app "plus" [var "x", var "y"]])
  ]

runNatPlus :: Maybe [MRule]
runNatPlus = huet natPlusPrec natPlusAxioms
-- putStrLn (pretty runNatPlus)

-- succeed
zeroMonoidPrec :: Prec
zeroMonoidPrec = precFromList ["f", "z", "e"]

leftZeroAx :: Equation
leftZeroAx =
  Equation
    (app "f" [app "z" [], var "x"])
    (app "z" [])

zeroMonoidAxioms :: [Equation]
zeroMonoidAxioms =
  [ monoidAx1
  , monoidAx2
  , monoidAx3
  , leftZeroAx
  ]

runZeroMonoid :: Maybe [MRule]
runZeroMonoid = huet zeroMonoidPrec zeroMonoidAxioms
-- putStrLn (pretty runZeroMonoid)

-- example from wikipedia
one :: Term
one = app "e" []

cx :: Term
cx = app "x" []

cy :: Term
cy = app "y" []

mul :: Term -> Term -> Term
mul a b = app "f" [a, b]

pow :: Term -> Int -> Term
pow t 1 = t
pow t n = mul t (pow t (n - 1))

wikiPrec :: Prec
wikiPrec = precFromList ["f", "x", "y", "e"]

wikiMonoidAxioms :: [Equation]
wikiMonoidAxioms =
  [ Equation (mul one (var "z")) (var "z")
  , Equation (mul (var "z") one) (var "z")
  , Equation (mul (mul (var "a") (var "b")) (var "c"))
             (mul (var "a") (mul (var "b") (var "c")))
  , Equation (pow cx 3) one
  , Equation (pow cy 3) one
  , Equation (pow (mul cx cy) 3) one
  ]

runWikiMonoid :: Maybe [MRule]
runWikiMonoid = huet wikiPrec wikiMonoidAxioms
-- putStrLn (pretty runWikiMonoid)