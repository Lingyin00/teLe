{-# LANGUAGE GADTs #-}
module Term where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set

newtype Var = Var String -- newtype creates a real new different type
    deriving (Eq, Ord, Show)
newtype FuncSym = FuncSym String
    deriving (Eq, Ord, Show)
-- DEF：Σ ∩ X = ∅ infinitely many

-- a signature is a list of function symbols with arity
type Signature = Map FuncSym Int 
--exampleSig :: Signature
--exampleSig = Map.fromList [("0", 0), ("f", 1), ("+", 2)]

data Term where
    VarT :: Var -> Term
    FunAppT :: FuncSym -> [Term] -> Term
    deriving(Eq, Ord, Show)

-- wellformedness over a signature
wellFormed :: Signature -> Term -> Bool
wellFormed _ (VarT _) = True -- a variable is always wellformed
wellFormed sig (FunAppT f ts) =
    case Map.lookup f sig of
        Just n ->  length ts == n && all (wellFormed sig) ts
        Nothing -> False

-- a term is ground iff. it doesn't contain any variables
isGround :: Term -> Bool
isGround (VarT _) = False
isGround (FunAppT _ ts) = all isGround ts
-- isGround (FunAppT (FuncSym "f") [FunAppT (FuncSym "0") []]) : True
-- isGround (FunAppT (FuncSym "f") [VarT (Var "x")]): False

-- set of variables which appear in a term
vars :: Term -> Set Var
vars (VarT t) = Set.singleton t
vars (FunAppT _ ts) = Set.unions (map vars ts)

-- set of function symbols which appear in a term
funSymbols :: Term -> Set FuncSym
funSymbols (VarT _) = Set.empty
funSymbols (FunAppT t ts) = Set.insert t $ Set.unions (map funSymbols ts)

-- constructor helper
-- app "f" [ app "f" [var "x"], app "g" [] ]
var :: String -> Term
var x = VarT (Var x)
app :: String -> [Term] -> Term
app f ts = FunAppT (FuncSym f) ts

-- the root symbol of a term: 
-- either a variable or a function symbol
data Root =
    RootVar Var
    | RootFun FuncSym
    deriving (Eq, Ord, Show)

root :: Term -> Root
root (VarT t) = RootVar t
root (FunAppT f _) = RootFun f

-- size of a term
sizeOfT :: Term -> Int 
sizeOfT (VarT _) = 1
sizeOfT (FunAppT _ ts) = 1 + sum (map sizeOfT ts)

-- height of a term

-- whether a term t is a subterm of s

-- position

-- substitution

