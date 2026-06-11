{-# OPTIONS_GHC -Wincomplete-patterns #-}
{-# LANGUAGE GADTs #-}
module Term where
{- ============================================================================
   Term — first-order terms over a signature  T(Σ, X)
   ============================================================================

   Representation
     data Term            VarT / FunAppT      -- inductive def of T(Σ, X)
     newtype Var          variables (X)       -- newtype keeps Σ ∩ X = ∅ at type level
     newtype FuncSym      function symbols (Σ)
     data Root            RootVar / RootFun    -- a root is a Var or a FuncSym
     type Signature       Map FuncSym Int      -- Σ = (F, arity): symbol ↦ arity
     type Pos             [Int]                -- positions; ε = [], 0-based

   Construction helpers
     var  :: String -> Term                    -- var "x"     = VarT (Var "x")
     app  :: String -> [Term] -> Term          -- app "f" [..] = FunAppT (FuncSym "f") [..]

   Predicates / queries
     wellFormed :: Signature -> Term -> Bool    -- f ∈ Σ and arity(f) = #children, recursively
     isGround   :: Term -> Bool                 -- contains no variables
     isSub      :: Term -> Term -> Bool         -- s ⊴ t : s is a subterm of t (reflexive)

   Collecting
     vars       :: Term -> Set Var              -- variables occurring in t
     funSymbols :: Term -> Set FuncSym          -- function symbols occurring in t
     root       :: Term -> Root                 -- top symbol of t

   Measures
     sizeOfT    :: Term -> Int                  -- number of nodes
     heightOfT  :: Term -> Int                  -- height/depth; vars and constants = 0

   Positions (rewriting substrate)
     positions  :: Term -> [Pos]                      -- all positions Pos(t)
     subtermAt  :: Term -> Pos -> Maybe Term          -- t|_p ; Nothing on illegal p
     replaceAt  :: Term -> Pos -> Term -> Maybe Term  -- t[s]_p ; Nothing on illegal p
     replaceNth :: Int -> a -> [a] -> [a]             -- helper: replace one list element

   Conventions
     - Positions 0-based; ε = []. subtermAt/replaceAt are partial → Maybe.
   ============================================================================ -}
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

-- the root symbol of a term is either a variable or a function symbol
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

-- height (or depth) of a term
heightOfT :: Term -> Int
heightOfT (VarT _) = 0
heightOfT (FunAppT _ ts) = 
    case length ts of
        0 -> 0
        _ -> 1 + maximum (map heightOfT ts)

-- whether a term s is a subterm of t
isSub :: Term -> Term -> Bool
isSub s t = s == t 
    || case t of
        FunAppT _ ts -> any (isSub s) ts
        VarT _ -> False

-- positions of a term, where root is defined as ε， and the first position begins with 0
type Pos = [Int]
positions :: Term -> [Pos]
positions (VarT _) = [[]]
positions (FunAppT _ ts) = [] : concat (prefixed)
    where 
        prefixed = [map (i:) (positions ti) | (i, ti) <- zip [0..] ts]

-- take a subterm of a term at a particular position
subtermAt :: Term -> Pos -> Maybe Term
subtermAt t [] = Just t
subtermAt (FunAppT _ ts) (x : xs) 
    | x >= 0 && x < length ts = subtermAt (ts !! x) xs
    | otherwise = Nothing
subtermAt _ _ = Nothing

-- t[s]_p: replace subterm at position p by s.
-- Nothing if p is illegal (out-of-range index, or descending into a variable)
replaceAt :: Term -> Pos -> Term -> Maybe Term
replaceAt _ [] s = Just s  -- directly repalce the term as s, if it happens at the root
replaceAt (FunAppT f ts) (x : xs) s 
    | x >= 0 && x < length ts = 
        case replaceAt (ts !! x) xs s of
            Just newChild ->
                Just (FunAppT f (replaceNth x newChild ts))
            Nothing -> Nothing
    | otherwise = Nothing
replaceAt _ _ _ = Nothing

replaceNth :: Int -> a -> [a] -> [a]
replaceNth n y xs = [if j == n then y else xj | (j, xj) <- zip [0..] xs]
