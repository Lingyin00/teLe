module Repl
  ( module Examples
  , module Huet
  , module LPO
  , module Rewrite
  , module Term
  , module TptpParser
  , solveTptp
  ) where

import Examples
import Huet
import LPO
import Rewrite
import Term
import TptpParser

solveTptp :: Prec -> String -> Either String Bool
solveTptp prec s = do
  (axs, goal) <- parseAxiomsAndGoal s
  case huetRules (huet prec axs) of
    Nothing -> Left "completion failed (orient/diverge)"
    Just rs -> Right (decideEq rs goal)