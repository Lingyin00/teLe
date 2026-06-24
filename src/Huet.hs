module Huet where

-- Implementation of the `Huet´s completion procedure` according to `TRaAT` written by Nipkow & Baader
-- Input: Set E of identities, Terminating set R of rewrite rules
-- rules may be marked or not(for computing critical pairs)
import Term
import Rewrite
import LPO
import CriticalPair

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

-- fairness : rules with marker
data MRule = MRule{
    mrule :: Rule,
    marked :: Bool}

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

-- helper: divide the rls into rules which can be reduced by newRule and which can not



huet :: Prec -> [Equation] -> Maybe [MRule]
huet p es = runFresh(outer es [])
  where -- es = E_0, [] = R_0
    -- TODO: Is preprocessing needed here??
    outer :: [Equation] -> [MRule] -> Fresh(Maybe [MRule])
    outer eqs rls 
      | null eqs && allMarked rls = pure(Just rls)
      | otherwise = do-- enter into the inner loop
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
                                outer newEqs newRls
    inner :: [Equation] -> [MRule] -> Fresh(Maybe [MRule]) -- step from a to e
    inner [] rls = pure (Just rls)
    inner (eq : eqs) rls = do
        -- take one equation, which is eq here, normalize its lhs and its rhs
        let rls' = map mrule rls -- rule a) b)
            normal_lhs = normalize rls' (eql eq)
            normal_rhs = normalize rls' (eqr eq)
        if normal_lhs == normal_rhs then inner eqs rls
           else case orient p (Equation normal_lhs normal_rhs) of
                    Nothing -> pure Nothing -- rule d)
                    Just newRule -> undefined
                    -- filter out rules in R which cannot been reduced by newRule
                    -- keep the lhs of those rules and normalize rhs by R ∪ {newRule}, inherit marker
                    -- newRule is unmarked
                    -- add newRule to this new rule set
                    -- remove eq from the original equation set
                    -- add new equations to the equation set: new equations are from those reduced rules(keep the reduced lhs and keep rhs unchanged)



    