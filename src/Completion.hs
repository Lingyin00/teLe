module Completion where

import Unification
import LPO 
import CriticalPair
import Rewrite

-- ==================================================
-- the unfailing Knuth-Bendix Completion
-- ==================================================
-- step 1: using LPO and Prec to orient all the equations into rules
-- step 2: 



-- ==================================================
-- completionNaive :: Prec -> [Equation] -> Maybe [Rule]
-- TODO: look up the input, and remove the redundant rules
-- TODO: the unfailing loop
