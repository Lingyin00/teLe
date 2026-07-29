module Main where
import ExamplesFromKnuth as Knuth
import Decide 

main :: IO ()
main = do
  _ <- Knuth.runAll
  putStrLn ""
  _ <- Decide.runDecide
  pure ()

