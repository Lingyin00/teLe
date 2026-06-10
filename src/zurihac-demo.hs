module zurihac-demo where
import Data.List (nub)
import Data.Maybe

data Term where
  Variable :: String -> Term
  Function :: String -> [Term] -> Term
  deriving Show

isSub :: Term -> Term -> Bool
isSub (Variable x) (Variable y) = x==y
isSub (Function n1 xs) (Function n2 ys) =
  (n1 == n2) && all (isSubHelper ys) xs
isSub _ _ = False

isSubHelper :: [Term] -> Term -> Bool
isSubHelper ts t = any (isSub t) ts

f1,f2,f3 :: Term
f1 = Function "f1" [Variable "t1", Variable "t2", Variable "t3", Variable "t4"]
f2 = Function "f2" [Variable "t1", Variable "t2", Variable "t3", Variable "t4", Variable "t5"]
f3 = Function "f3" [Variable "t1", Variable "t2", Variable "t3", Variable "t5", f1]


printThis :: IO ()
printThis = do
  putStrLn "isSub f1 f2"
  print (isSub f1 f2)
  putStrLn "isSub f1 f3"
  print (isSub f1 f3)



substitute a b x = if x == a then b else x

type Substitution = Term -> Term
substitution :: (String -> String) -> Substitution
substitution f (Variable x) = Variable (f x)
substitution f (Function n xs) = Function n (map (substitution f) xs)


findVariables :: Term -> [String]
findVariables (Variable x) = [x]
findVariables (Function _ xs) = nub . concatMap findVariables $ xs


outf = Function "outf" [f1,f2,f3, Variable "t2"]


var = Variable



match :: Term -> Term -> Maybe [Substitution]
match (Variable a) (Variable b)
  | a == b = Just []
  | otherwise =  Just [substitution (substitute a b)]
match (Function f1 xs) (Function f2 ys)
  | f1 /= f2 = Nothing
  | length f1 /= length f2 = Nothing
  | otherwise =  helper . zipWith match xs $ ys
match _ _ = Nothing

helper :: [Maybe [Term -> Term]] -> Maybe [Substitution]
helper xs = if any isNothing xs then Nothing else
    Just (concat . catMaybes $ xs)

fun1 = Function "f" [var "x", var "y"]
fun2 = Function "f" [var "y", var "y"]

out = fromJust . match fun1 $ fun2


