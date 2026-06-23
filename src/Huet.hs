module Huet where

-- Implementation of the `Huet´s completion procedure` according to `TRaAT`
-- Input: Set E of identities, Terminating set R of rewrite rules
-- rules may be marked or not(for computing critical pairs)
import Term
import Rewrite
import LPO
import CriticalPair
-- TODO : orient an equation by using term ordering
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

-- Begins here: the Huet's completion loop

-- TODO : deduce
-- TODO : findMarked
-- TODO : mark
-- TODO : allMarked
-- TODO : processEquation (step b, c, d, e)

-- fairness : rules are with marker
data MRule = MRule{
    mrule :: Rule,
    marked :: Bool}

-- psudocode in Haskell style of Huet's completion with outer loop and inner loop
-- outer e r
--  | null e && allMarked r = Just r
--  | otherwise =
--      case inner e r of
--          Nothing -> Nothing -- completion fails
--          Just r' -> case findMarked r' of
                        -- Nothing -> Just r'
                        -- Just (r1， r'') -> outer (deduce r1 r'') (mark r1 r'')
-- inner e r
--   | null e = Just r
--   | otherwise =
--          let (x : rest) = e in case processEquation x r of
            -- Fail -> Nothing
            -- Delete r' -> inner rest r'
            -- Orient newE r'  -> inner (newE ++ rest) r'          

huet :: Prec -> [Equation] -> Maybe [Rule]
--huet p es = 
