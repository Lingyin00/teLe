{-# OPTIONS_GHC -Wincomplete-patterns #-}

-- | A small, self-contained parser for the *pure-equality* fragment of TPTP FOF.
--
--   It is deliberately limited to exactly what the completion kernel can consume:
--   universally-quantified single equations.  Anything outside that fragment
--   (logical connectives &/|/=>/<=>, existential quantifiers, non-equality
--   predicates) is rejected with a descriptive error, rather than silently
--   mis-parsed.  This mirrors the equational-logic boundary of the kernel:
--   quantifier handling and clausification belong to a first-order front end,
--   not here.
--
--   Supported input shape (whitespace/newlines flexible):
--
--     fof( name , axiom ,      ! [A,B] : lhs = rhs ).
--     fof( name , conjecture , ! [X]   : lhs = rhs ).
--     fof( name , axiom ,      lhs = rhs ).            -- quantifier optional
--
--   Comment lines starting with '%' and blank lines are ignored.
--
--   Output:
--     parseEquations      :: String -> Either String [Equation]
--     parseAxiomsAndGoal  :: String -> Either String ([Equation], Equation)
--
--   Variable convention: TPTP upper-case identifiers (A, B, X0, ...) become
--   'VarT'; everything else (lower-case names, numbers used as constants)
--   becomes a 'FunAppT'.  A 0-ary application 'app "c" []' is a constant.

module TptpParser
  ( parseEquations
  , parseAxiomsAndGoal
  , parseTerm
  , Role(..)
  , parseUnits
  ) where

import Data.Char (isSpace, isAlpha, isAlphaNum, isUpper, isDigit)
import Data.List (foldl', isPrefixOf, stripPrefix)
import Term (Term, var, app)
import Rewrite (Equation(..))

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

data Role = RAxiom | RHypothesis | RConjecture
  deriving (Eq, Show)

-- | Parse every unit, returning (role, equation) pairs in file order.
parseUnits :: String -> Either String [(Role, Equation)]
parseUnits input = do
  let toks = lexTptp (stripComments input)
  units <- splitUnits toks
  mapM parseUnit units

-- | All equations regardless of role (axioms + conjectures together).
parseEquations :: String -> Either String [Equation]
parseEquations s = map snd <$> parseUnits s

-- | Split into (axioms+hypotheses, the single conjecture).
--   Errors if there is not exactly one conjecture.
parseAxiomsAndGoal :: String -> Either String ([Equation], Equation)
parseAxiomsAndGoal s = do
  units <- parseUnits s
  let goals = [e | (RConjecture, e) <- units]
      axs   = [e | (r, e) <- units, r /= RConjecture]
  case goals of
    [g] -> Right (axs, g)
    []  -> Left "no conjecture found"
    _   -> Left ("expected exactly one conjecture, found " ++ show (length goals))

-- | Parse a single term from a string (handy for ghci testing).
parseTerm :: String -> Either String Term
parseTerm s =
  case runP pTerm (lexTptp s) of
    Right (t, []) -> Right t
    Right (_, rest) -> Left ("unexpected trailing tokens: " ++ show rest)
    Left e -> Left e

-- ---------------------------------------------------------------------------
-- Tokenizer
-- ---------------------------------------------------------------------------

data Tok
  = TIdent String   -- identifier or number
  | TLParen
  | TRParen
  | TLBracket
  | TRBracket
  | TComma
  | TDot
  | TEq             -- =
  | TNeq            -- != (we record it so we can give a good error)
  | TBang           -- !  (forall)
  | TQuestion       -- ?  (exists)  -> will trigger a clear rejection
  | TColon          -- :
  | TConn String    -- &  |  =>  <=  <=>  <~>  ~   (connectives -> rejected)
  deriving (Eq, Show)

stripComments :: String -> String
stripComments = unlines . map dropComment . lines
  where
    -- TPTP line comments start with %.  (Block comments /* */ are rare in the
    -- equality problems we target; handled crudely below if present.)
    dropComment ln = takeWhile (/= '%') ln

lexTptp :: String -> [Tok]
lexTptp [] = []
lexTptp (c:cs)
  | isSpace c            = lexTptp cs
  | c == '('             = TLParen   : lexTptp cs
  | c == ')'             = TRParen   : lexTptp cs
  | c == '['             = TLBracket : lexTptp cs
  | c == ']'             = TRBracket : lexTptp cs
  | c == ','             = TComma    : lexTptp cs
  | c == '.'             = TDot      : lexTptp cs
  | c == '!'             = TBang     : lexTptp cs
  | c == '?'             = TQuestion : lexTptp cs
  | c == ':'             = TColon    : lexTptp cs
  | c == '&'             = TConn "&" : lexTptp cs
  | c == '|'             = TConn "|" : lexTptp cs
  | c == '~'             = case cs of
                             ('&':r) -> TConn "~&" : lexTptp r
                             ('|':r) -> TConn "~|" : lexTptp r
                             _       -> TConn "~"  : lexTptp cs
  | c == '='             = case cs of
                             ('>':r) -> TConn "=>" : lexTptp r
                             _       -> TEq        : lexTptp cs
  | c == '<'             = case cs of
                             ('=':'>':r) -> TConn "<=>" : lexTptp r
                             ('~':'>':r) -> TConn "<~>" : lexTptp r
                             ('=':r)     -> TConn "<="  : lexTptp r
                             _           -> TConn "<"   : lexTptp cs
  | c == '/' , ('*':r) <- cs = lexTptp (dropBlock r)  -- /* ... */
  | isIdentStart c       = let (nm, rest) = span isIdentChar (c:cs)
                           in TIdent nm : lexTptp rest
  | c == '\'' = let (nm, rest) = break (== '\'') cs   -- 'quoted name'
                in TIdent nm : lexTptp (drop 1 rest)
  | otherwise            = error ("lexTptp: unexpected character " ++ show c)
  where
    isIdentStart x = isAlpha x || x == '_' || isDigit x || x == '$'
    isIdentChar  x = isAlphaNum x || x == '_' || x == '$'
    dropBlock ('*':'/':r) = r
    dropBlock (_:r)       = dropBlock r
    dropBlock []          = []

-- handle != which the single-char lexer split into TConn "~"? No: '!' then '='.
-- We post-process the token stream to merge [TBang, TEq] that came from "!=".
-- Simpler: detect '!=' at lex time. Re-do via a fixup pass:
fixupNeq :: [Tok] -> [Tok]
fixupNeq (TBang : TEq : r) = TNeq : fixupNeq r
fixupNeq (t : r)           = t : fixupNeq r
fixupNeq []                = []

-- ---------------------------------------------------------------------------
-- A tiny parser combinator over [Tok]
-- ---------------------------------------------------------------------------

newtype P a = P { runP :: [Tok] -> Either String (a, [Tok]) }

instance Functor P where
  fmap f (P g) = P $ \ts -> case g ts of
    Right (a, r) -> Right (f a, r)
    Left e       -> Left e

instance Applicative P where
  pure x = P $ \ts -> Right (x, ts)
  P f <*> P x = P $ \ts -> case f ts of
    Right (g, r) -> case x r of
      Right (a, r') -> Right (g a, r')
      Left e -> Left e
    Left e -> Left e

instance Monad P where
  P g >>= f = P $ \ts -> case g ts of
    Right (a, r) -> runP (f a) r
    Left e -> Left e

pErr :: String -> P a
pErr msg = P $ \_ -> Left msg

peek :: P (Maybe Tok)
peek = P $ \ts -> case ts of
  (t:_) -> Right (Just t, ts)
  []    -> Right (Nothing, ts)

tok :: Tok -> P ()
tok expected = P $ \ts -> case ts of
  (t:r) | t == expected -> Right ((), r)
  (t:_)                 -> Left ("expected " ++ show expected ++ ", got " ++ show t)
  []                    -> Left ("expected " ++ show expected ++ ", got end of input")

ident :: P String
ident = P $ \ts -> case ts of
  (TIdent s : r) -> Right (s, r)
  (t:_)          -> Left ("expected identifier, got " ++ show t)
  []             -> Left "expected identifier, got end of input"

-- ---------------------------------------------------------------------------
-- Splitting the token stream into units terminated by '.'
-- ---------------------------------------------------------------------------

splitUnits :: [Tok] -> Either String [[Tok]]
splitUnits = go [] . fixupNeq
  where
    go acc [] = case acc of
      [] -> Right []
      _  -> Left "trailing tokens without terminating '.'"
    go acc (TDot : r) = (reverse acc :) <$> go [] r
    go acc (t : r)    = go (t : acc) r

-- ---------------------------------------------------------------------------
-- Parsing one unit:  fof ( name , role , <formula> )
-- ---------------------------------------------------------------------------

parseUnit :: [Tok] -> Either String (Role, Equation)
parseUnit ts = fst <$> runP unit ts
  where
    unit = do
      kw <- ident
      case kw of
        "fof" -> pure ()
        "cnf" -> pure ()
        other -> pErr ("expected 'fof' or 'cnf', got " ++ show other)
      tok TLParen
      _name <- ident
      tok TComma
      roleStr <- ident
      role <- case roleStr of
        "axiom"             -> pure RAxiom
        "hypothesis"        -> pure RHypothesis
        "conjecture"        -> pure RConjecture
        "negated_conjecture"-> pure RConjecture
        "plain"             -> pure RAxiom
        other               -> pErr ("unsupported role: " ++ other)
      tok TComma
      eq <- pFormula
      tok TRParen
      pure (role, eq)

-- A formula in our fragment: optional leading quantifier(s), then an equation.
pFormula :: P Equation
pFormula = do
  mt <- peek
  case mt of
    Just TBang     -> pQuantified
    Just TLParen   -> do tok TLParen
                         eq <- pFormula
                         tok TRParen
                         pure eq
    Just TQuestion -> pErr "existential quantifier (?) is outside the equational fragment \
                           \this kernel handles; needs a first-order front end"
    Just (TConn c) -> pErr ("logical connective '" ++ c ++ "' is outside the equational \
                            \fragment; needs clausification in a first-order front end")
    _              -> pEquation

-- ! [vars] : <formula>
pQuantified :: P Equation
pQuantified = do
  tok TBang
  tok TLBracket
  _vs <- pVarList
  tok TRBracket
  tok TColon
  pFormula        -- variables are implicitly universal in equational logic; we
                  -- simply drop the binder and parse the body.

pVarList :: P [String]
pVarList = do
  v <- ident
  mt <- peek
  case mt of
    Just TComma -> tok TComma >> ((v :) <$> pVarList)
    _           -> pure [v]

-- lhs = rhs   (and reject lhs != rhs / connective-joined equations)
pEquation :: P Equation
pEquation = do
  l <- pTerm
  mt <- peek
  case mt of
    Just TEq  -> do tok TEq
                    r <- pTerm
                    afterEq
                    pure (Equation l r)
    Just TNeq -> pErr "disequality (!=) found: this is a CNF refutation literal, not a \
                      \positive equational axiom/goal; feed the original FOF conjecture instead"
    Just (TConn c) -> pErr ("connective '" ++ c ++ "' joining equations is outside the \
                            \equational fragment")
    other -> pErr ("expected '=' after term, got " ++ show other)
  where
    -- after a complete equation we must be at ')' (end of fof) — nothing else.
    afterEq = do
      mt <- peek
      case mt of
        Just (TConn c) -> pErr ("connective '" ++ c ++ "' after equation is outside the \
                                \equational fragment")
        _ -> pure ()

-- ---------------------------------------------------------------------------
-- Terms:  ident                      -> constant or variable
--         ident ( t , t , ... )      -> function application
-- ---------------------------------------------------------------------------

pTerm :: P Term
pTerm = do
  name <- ident
  mt <- peek
  case mt of
    Just TLParen -> do
      tok TLParen
      args <- pArgs
      tok TRParen
      pure (app name args)
    _ ->
      pure (mkAtom name)
  where
    mkAtom name
      | isVarName name = var name
      | otherwise      = app name []   -- 0-ary constant

pArgs :: P [Term]
pArgs = do
  t <- pTerm
  mt <- peek
  case mt of
    Just TComma -> tok TComma >> ((t :) <$> pArgs)
    _           -> pure [t]

-- TPTP convention: variables are upper-case-initial; functors/constants are
-- lower-case-initial (or numbers, or $-prefixed).  We follow that.
isVarName :: String -> Bool
isVarName (c:_) = isUpper c
isVarName []    = False
