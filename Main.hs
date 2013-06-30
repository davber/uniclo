module Main where

import Prelude hiding (catch, lex)
import Control.Applicative hiding (many, optional)
import Text.ParserCombinators.Parsec hiding (State, (<|>))
import Text.ParserCombinators.Parsec.Token as P
import Text.Parsec.Numbers as Num
import Text.ParserCombinators.Parsec.Char
import Text.Parsec.Language (haskellDef)
import Data.Either
import Data.Maybe
import Data.Char
import qualified Data.Set as S
import qualified Data.Map as M
import Data.String.Utils as Str
import Data.List.Utils
import Data.List(sort, group)
import Control.Monad.Error
import Control.Monad.State
import Control.Exception hiding (try)
import qualified Data.Map as Map
import Text.Show.Functions

--
-- Some common notions, for all phases
--

type Err = String

name :: Expr -> Maybe String
name (ESymbol s) = Just s
name _ = Nothing

--
-- S-Exprs and more semantic representations; i.e., we combine syntax
-- and (denotational) semantics, in a Herbrand manner
--

type Function = [Param] -> Computation
data Lambda = Lambda String Expr Expr Function
instance Show Lambda where
  show (Lambda name params expr _) = name ++
    if isTruthy params then ": " ++ show params ++ " --> " ++ show expr ++ ")" else ""
type Param = Expr
data SeqType = SeqList | SeqVector | SeqMap | SeqSet | SeqString  deriving (Show, Read, Eq, Ord)
leftDelim SeqList = "("
leftDelim SeqVector = "["
leftDelim SeqSet = "#{"
leftDelim SeqMap = "{"
rightDelim SeqList = ")"
rightDelim SeqVector = "]"
rightDelim SeqSet = "}"
rightDelim SeqMap = "}"

-- is the expression a proper sequence already?
-- NOTE: expressions can be seqable, turned into a sequence by seqElems
isSeq :: Expr -> Bool
isSeq (EList _) = True
isSeq (EVector _) = True
isSeq (ESet _) = True
isSeq (EMap _) = False
isSeq (EString _) = False
isSeq _ = False

-- is the expression comvertible into a sequence, i.e., seqable?
isSeqable :: Expr -> Bool
isSeqable e | isSeq e = True
isSeqable (EString _) = True
isSeqable (EMap _) = True
isSeqable _ = False

-- can expression contain sub expressions?
isContainer :: Expr -> Bool
isContainer e | isSeq e = True
isContainer (EMap _) = True
isContainer _ = False

seqType (EList _) = SeqList
seqType (EVector _) = SeqVector
seqType (ESet _) = SeqSet
seqType (EMap _) = SeqMap

seqElems :: Expr -> [Expr]
seqElems (EList es) = es
-- NOTE: the elements are stored in reverse inside the vector construct
seqElems (EVector es) = reverse es
seqElems (ESet s) = S.elems s
seqElems (EMap m) = map (\(k,v) -> makeSeq SeqVector [k, v]) $  M.assocs m
seqElems (EString s) = map (\c -> EChar c) s
seqElems x = []

isEmpty :: Expr -> Bool
isEmpty s = case seqElems s of
  (_:_) -> True
  _ -> False

seqFirst :: Expr -> Expr
seqFirst e = let elems = seqElems e in
  if null elems then ENil else head elems

seqRest :: Expr -> [Expr]
seqRest e = let elems = seqElems e in
  if null elems then [] else tail elems

-- make a seqable object from a natural sequence of elements for that type
makeSeq :: SeqType -> [Expr] -> Expr
makeSeq SeqList = EList
makeSeq SeqSet = ESet . S.fromList
makeSeq SeqVector = EVector . reverse
-- NOTE: the sequence provided to a map consists of binary sequences, holding key and value
makeSeq SeqMap = EMap . M.fromList . map (\elem -> let (k:v:[]) = seqElems elem in (k,v))

-- create pairs of consecutive elements, in the form of EVectors
pairs :: [Expr] -> [Expr]
pairs [] = []
pairs (a:b:r) = makeSeq SeqVector [a, b] : pairs r
pairs [a] = [makeSeq SeqVector [a, ENil]] -- TODO: ad hoc for a strange case...

-- make a seqable object from a flat list of elements
makeSeqFlat :: SeqType -> [Expr] -> Expr
makeSeqFlat SeqMap = makeSeq SeqMap . pairs
makeSeqFlat seqType = makeSeq seqType

conj :: Expr -> Expr -> Expr
conj (EList s) e = EList (e:s)
-- NOTE: the vector is stored in reverse inside the construct
conj (EVector s) e = EVector (e : s)
-- NOTE: conj:ing to a map requires a seqable element with at least two
-- elements, being the new key and value to be added
conj (EMap m) e = let (k:v:_) = seqElems e in EMap $ M.insert k v m
conj (ESet s) e = ESet $ S.insert e s

data Expr = EKeyword String (Maybe String) | ESymbol String | ENumber Integer |
            EString String | EChar Char | EBool Bool | ENil | Fun Lambda | Macro Lambda | ESpecial String Function | EList [Expr] | EVector [Expr] | ESet (S.Set Expr) | EMap (M.Map Expr Expr)
instance Show Expr where
  show (EKeyword s Nothing) = ":" ++ s
  show (EKeyword s (Just ns)) = ":" ++ ns ++ "/" ++ s
  show (ESymbol s) = s
  show (EString s) = "\"" ++ s ++ "\""
  show (EChar c) = "\\" ++ showLitChar c ""
  show (ENumber num) = show num
  show (EBool b) = if b then "true" else "false"
  show ENil = "nil"
  show (Fun lambda) = "[fun]" ++ show lambda
  show (Macro lambda) = show lambda
  show (ESpecial s _) = "[special]" ++ s
  show (EMap m) = "{" ++ Str.join ", " (map (\(k,v) -> show k ++ " " ++ show v) $ M.assocs m) ++ "}"
  show e | isContainer e = leftDelim (seqType e) ++ (Str.join " " $ map show elems) ++ rightDelim (seqType e) where
    elems = seqElems e
instance Eq Expr where
  EKeyword ns1 s1 == EKeyword ns2 s2 = ns1 == ns2 && s1 == s2
  ESymbol s1 == ESymbol s2 = s1 == s2 
  EChar c1 == EChar c2 = c1 == c2
  ENumber num1 == ENumber num2 = num1 == num2
  EString s1 == EString s2 = s1 == s2
  EBool b1 == EBool b2 = b1 == b2
  ENil == ENil = True
  Fun (Lambda n1 p1 e1 _) == Fun (Lambda n2 p2 e2 _) = n1 == n2 && e1 == e2 && p1 == p2
  ESpecial s1 _ == ESpecial s2 _ = s1 == s2
  seq1 == seq2 | isContainer seq1 && isContainer seq2 =
    seqType seq1 == seqType seq2 && seqElems seq1 == seqElems seq2
  _ == _ = False
lexico comps = if length diffs == 0 then EQ else head diffs where diffs = filter (/= EQ) comps
instance Ord Expr where
  EKeyword ns1 s1 `compare` EKeyword ns2 s2 = lexico [ns1 `compare` ns2, s1 `compare` s2]
  ESymbol s1 `compare` ESymbol s2 = s1 `compare` s2
  ENumber s1 `compare` ENumber s2 = s1 `compare` s2
  EString s1 `compare` EString s2 = s1 `compare` s2
  seq1 `compare` seq2 | isContainer seq1 && isContainer seq2 =
    (seqType seq1, seqElems seq1) `compare` (seqType seq2, seqElems seq2)
  e1 `compare` e2 = show e1 `compare` show e2
type ParseResult = Either Err [Expr]

exprType :: Expr -> String
exprType (Fun {}) = "fun"
exprType (EKeyword {}) = "keyword"
exprType (ENumber {}) = "number"
exprType (ESymbol {}) = "symbol"
exprType (EChar {}) = "char"
exprType (EString {}) = "string"
exprType (ENil {}) = "nil"
exprType (ESpecial {}) = "special"
exprType (EMap {}) = "map"
exprType (EList {}) = "list"
exprType (EVector {}) = "vector"
exprType (ESet {}) = "set"
exprType e | isSeqable e = "seq"
exprType e = "none"

--
-- Environment
--
-- Has a global binding and a local binding
--

-- Expressions evaluate to Herbrand values
type Value = Expr

-- The computation monad has to handle
type Bindings = Map.Map String Value
data Env = Env { globalEnv :: Bindings, localEnv :: Bindings, traceFlag :: Bool } deriving (Show)

setTrace :: Bool -> ComputationM Bool
setTrace flag = do
  env <- get
  let oldFlag = traceFlag env
  let env' = env { traceFlag = flag }
  put env'
  return oldFlag
getTrace :: ComputationM Bool
getTrace = get >>= return . traceFlag
printTrace :: String -> ComputationM ()
printTrace text = do
  flag <- getTrace
  if flag then liftIO $ putStrLn $ "TRACE: " ++ text else return ()

trace :: Expr -> IO ()
trace = print

printShow :: Expr -> String
printShow (EString s) = s
printShow x = show x

printEnv :: Env -> IO ()
printEnv e = do
  putStrLn $ "trace = " ++ show (traceFlag e)
  putStrLn "global"
  printBindings $ globalEnv e
  putStrLn "local"
  printBindings $ localEnv e

printBindings :: Bindings -> IO ()
printBindings bindings = do
  let pairs = Map.toList bindings
  mapM_ (\(k, v) -> putStr ("'" ++ k ++ "' = ") >> print v) pairs

-- Unify two tems, with bindings to the left, yielding the new binding,
-- if succeding
unify :: Expr -> Expr -> Bindings -> (Maybe Bindings)
unify (ESymbol name) value b = return $ Map.insert name value b
unify s1 s2 b | isSeqable s1 && isSeqable s2 = unifyList (seqElems s1) (seqElems s2) b
unify s1 s2 b | s1 == s2 = Just b
              | True = Nothing

unifyList :: [Expr] -> [Expr] -> Bindings -> (Maybe Bindings)
unifyList [] [] = return
unifyList (ESymbol "&" : rest : _) other = unify rest (EList other)
unifyList (f1:r1) (f2:r2) = (\b -> unify f1 f2 b >>= unifyList r1 r2)
unifyList _ _ = (\_ -> Nothing)

-- Computations can either (i) yield a value or (ii) yield an error
-- AND can also interact with the environment
-- We encapsulate this by a three-layer monadic pie:
-- Error - State - IO

type ComputationM = ErrorT Err (StateT Env IO)
type Computation = ComputationM Value

printComp :: Computation
printComp = do
  e <- get
  liftIO $ printEnv e
  return ENil

getVar :: Env -> String -> Maybe Value
getVar e var = listToMaybe $ catMaybes [(Map.lookup var $ localEnv e),
                                        (Map.lookup var $ globalEnv e)]

bindVar :: Env -> String -> Value -> Env
bindVar e k v = e { globalEnv = Map.insert k v $ globalEnv e }

resetLocal :: Env -> Env
resetLocal env = env { localEnv = createEmptyBindings }

setLocalEnv :: Bindings -> ComputationM ()
setLocalEnv bindings = do
  e <- get
  put $ e { localEnv = bindings }

createEmptyBindings :: Bindings
createEmptyBindings = Map.empty

createBindings :: [String] -> [Value] -> Bindings
createBindings keys values = foldl (\e (k,v) -> Map.insert k v e) Map.empty $ zip keys values

-- Create an environment only having mappings for special forms and primitive functions

createEmptyEnv :: Env
createEmptyEnv = let (primKeys, primValues) = unzip . map (\n -> (n, makePrimLambda n)) $ primFuns
                     (specialKeys, specialValues) = unzip. map (\n -> (n, makePrimSpecial n)) $ primSpecials in Env { traceFlag = False, globalEnv = createBindings (primKeys ++ specialKeys ++ [
  -- primitives
  "nil", "false", "true"])
  (primValues ++ specialValues ++ [
   ENil,
   EBool False,
   EBool True]),
   localEnv = createEmptyBindings }

-- utility to compose an unary function with a binary one
(.*) = (.) . (.)

createEmptyState :: Computation
createEmptyState = put createEmptyEnv >> return ENil

combineEnv :: Env -> Bindings -> Env
combineEnv e bindings = e { localEnv = Map.union bindings $ localEnv e }

unifyEnv :: Env -> Expr -> Expr -> Maybe Env
unifyEnv e e1 e2 = unify e1 e2 createEmptyBindings >>= return . (combineEnv e)

flipNs (EKeyword ns (Just s)) = EKeyword s (Just ns)
flipNs x = x

-- Try unification, yielding a flag if bindings were created
unifyState :: Expr -> Expr -> ComputationM Bool
unifyState e1 e2 = do
  e <- get
  let (e', flag) = maybe (e, False) (\env -> (env, True)) $ unifyEnv e e1 e2
  printTrace $ "Unification: " ++ show e1 ++ " <|> " ++ show e2 ++ " ==> " ++
               if flag then show (localEnv e') else "failed!" 
  put e'
  return flag

--
-- The parser, using Parsec
--

-- The reader consists of parsing and then expanding the forms

-- The tokenizer

language = P.LanguageDef {
    commentStart = "",
    commentEnd = "",
    commentLine = ";",
    nestedComments = False,
    identStart = oneOf "!#$%&|*+-/<=>?_." <|> letter,
    identLetter = oneOf "!#$%&|*+-<=>?_.'" <|> alphaNum,
    opStart = oneOf "~#`'",
    opLetter = oneOf "@",
    reservedNames = [],
    reservedOpNames = [],
    caseSensitive = True
  }
lexer' = P.makeTokenParser language 
lexer = lexer' { whiteSpace = skipMany1 (char ',') <|> P.whiteSpace lexer' }
lex = P.lexeme lexer
ws = P.whiteSpace lexer
sym = P.symbol lexer
ident = P.identifier lexer
oper = P.operator lexer
parseProgram = ws *> many parseExpr <* eof
parsePadExpr = lex parseExpr
parseChar = EChar . getCharLiteral <$> (char '\\' *> (try ident <|> (anyChar >>= return . (:[]))))
parseString = EString <$> P.stringLiteral lexer <?> "string"
parseNumber =  ENumber <$> (try . lex) Num.parseIntegral <?> "number"
parseKeyword = flipNs .* EKeyword <$>
               lex (char ':' *>
                P.identifier lexer) <*>
               optionMaybe (char '/' *> ident)
               <?> "keyword"
parseSymbol = ESymbol <$> lex (ident <|> oper)
              <?> "symbol"
parseAtom =  choice [parseNumber, parseChar, parseString, parseKeyword, parseSymbol]
             <?> "atom"
parseSeq seqType = makeSeqFlat seqType <$> 
                   (sym (leftDelim seqType) *> many parseExpr <* sym (rightDelim seqType))
                   <?> "list"
parseList = parseSeq SeqList
parseVector = parseSeq SeqVector
parseSet = parseSeq SeqSet
parseMap = parseSeq SeqMap
parseExpr = parseList <|> parseVector <|> parseSet <|> parseMap <|> parseAtom

parseProgramText :: String -> ParseResult
parseProgramText input = either (Left . show) Right $ parse parseProgram "clojure" input
parseExprText :: String -> ParseResult
parseExprText input = either (Left . show) (Right . (\x -> [x])) $ parse parseExpr "clojure" input

-- applies macro expansion to a program
expandProgram :: [Expr] -> ComputationM [Expr]
expandProgram exprs = printTrace "*** Expanding program ***" >> mapM (\e -> expandMacro e >>= evalMacro) exprs
-- reading a program both parses and read-expands it
readProgram :: String -> ComputationM [Expr]
readProgram text = do
  printTrace "*** Parsing program ***"
  either throwError (\expr -> printTrace "*** Reading program ***" >> shufflePrefixList expr) $ parseProgramText text

--
-- Evaluator, yielding (and executing...) a computation
--

evalProgram :: [Expr] -> ComputationM [Value]
evalProgram exprs = printTrace "*** Evaluating program ***" >> mapM evalExpr exprs

evalExpr :: Expr -> Computation
evalExpr e@(EKeyword _ _) = return e
evalExpr e@(EChar _) = return e
evalExpr (ESymbol sym) = do env <- get
                            let value = getVar env sym
                            maybe (throwError $ "Symbol " ++ sym ++ " had no value") return value
evalExpr e@(EList (f : params)) = do
  fun <- evalExpr f
  res <- apply fun params
  printTrace $ "Reduction: " ++ show e ++ " ==> " ++ show res
  return res
evalExpr e@(ENumber n) = return e
evalExpr e@(EString s) = return e
evalExpr e@(Fun f) = return e
evalExpr e@(ESpecial n s) = return e
evalExpr e@(Macro f) = return e
evalExpr e@ENil = return e
evalExpr e | isSeqable e = do
  vals <- mapM evalExpr $ seqElems e
  return $ makeSeq (seqType e) vals
evalExpr expr = throwError $ "Could not evaluate " ++ show expr

-- evalStr evalues expression by expression, thus allowing for definitions
-- of reader macros
evalStr :: String -> ComputationM [Value]
evalStr s = readProgram s >>= expandProgram >>= evalProgram

isSpecial :: Expr -> Bool
isSpecial (ESpecial _ _) = True
isSpecial _ = False

numHandler :: ([Integer] -> Integer) -> Function
numHandler f params = do
  nums <- mapM num params
  return $ ENumber $ f nums

num :: Expr -> ComputationM Integer
num (ENumber numb) = return numb
num e = throwError $ show e ++ " is not a number"

isTruthy :: Expr -> Bool
isTruthy ENil = False
isTruthy (EBool False) = False
isTruthy _ = True

apply :: Value -> [Value] -> Computation
apply (Fun (Lambda _ _ _ f)) params = mapM evalExpr params >>= f
apply (Macro (Lambda _ _ _ f)) params = f params >>= evalExpr
apply (ESpecial _ f) params = f params
apply other args = throwError $ "Not a proper function application: " ++ show (EList (other : args))

isMacro :: Expr -> Bool
isMacro (Macro _) = True
isMacro _ = False

--
-- Reader prefix reshuffling, which makes prefix symbols regular prefix forms
-- NOTE: we only care about definitions of the *prefix-symbols* forms for controlling
-- these prefix symbols!
--

shufflePrefix :: Expr -> Computation
shufflePrefix defE@(EList [ESymbol "def", ESymbol "*prefix-symbols*", expr]) = do
  val <- evalExpr expr -- NOTE: usually a literal sequence
  e <- get
  let e' = bindVar e "*prefix-symbols*" val
  put e'
  printTrace $ "Set prefix symbols to " ++ show val
  syms <- prefixSymbols
  return defE
shufflePrefix (EList [ESymbol "def", sym, expr]) = do
  expr' <- shufflePrefix expr
  return . EList $ [ESymbol "def", sym, expr']
shufflePrefix e | isContainer e = do
  let elems = seqElems e
  shufflePrefixList elems >>= return . makeSeq (seqType e)
-- TODO: should we not recurse into other conglomerates?
shufflePrefix x = return x

shufflePrefixList :: [Expr] -> ComputationM [Expr]
-- whenever a prefix symbol is followed by enother one, we deal with it right-associatively
shufflePrefixList e@(first : rest) = do
  shuffleF <- shufflePrefix first
  shuffleR <- shufflePrefixList rest
  isPrefix <- isPrefixSymbol first
  let e' =  if isPrefix && not (null shuffleR)
            then EList [first, head shuffleR] : tail shuffleR
            else shuffleF : shuffleR
  if isPrefix then printTrace $ "Reader: " ++ show e ++ " ==> " ++ show e' else return ()
  return e'
shufflePrefixList [] = return []

-- expand top-level form one step, if possible
expandMacro1 :: Expr -> ComputationM (Maybe Expr)
expandMacro1 e@(EList ((Macro (Lambda n _ _ f)) : params)) = do
  val <- f params
  printTrace $ "Inside macroexpand-1: " ++ show e ++ " ==> " ++ show val
  return . Just $ val
expandMacro1 e@(EList (f : params)) = do
  env <- get
  (fval, _) <- lift $ lift $ runStateT (runErrorT $ expandMacro f >>= evalExpr) env
  either (\err -> printTrace ("warning when trying to expand form " ++ show e ++ ": " ++ show err) >> return Nothing) (\val -> if isMacro val then expandMacro1 (EList (val : params)) else return Nothing) fval
expandMacro1 e = return Nothing


-- apply macroexpand-1 repeatedly at top level till it yields no new value
expandMacroTop :: Expr -> Computation
expandMacroTop e = do
  exp <- expandMacro1 e
  if exp == Nothing then return () else printTrace $ "Expansion: " ++ show e ++ " ==> " ++ show exp
  maybe (return e) expandMacro exp

-- apply macroexpand both on top and then recursively inside the form
expandMacro :: Expr -> Computation
expandMacro e = do
  topExp <- expandMacroTop e
  let children = seqElems topExp
  if exprType topExp /= "string" && isContainer topExp && (not . null) children then do
    expChildren <- mapM expandMacro children
    return $ makeSeq (seqType topExp) expChildren
  else
    return topExp

-- the post-expansion evaluation that can take place during the macro expansion stage
-- TODO: this is currently only 'def' and 'defmacro' expressions at top level
-- NOTE: this always returns the original expression, even if it was evaluated for
-- side effects
macroEvaluable = ["def", "defmacro", "defn"]
evalMacro :: Expr -> Computation
evalMacro e@(EList (ESymbol sym : EString _ : _)) | elem sym macroEvaluable =
  printTrace ("Evaluating during expansion: " ++ show e) >> evalExpr e >> return e
evalMacro e = return e

main :: IO ()
main = repl createEmptyEnv

repl :: Env -> IO ()
repl env = do
  -- we emulate a loading of the prelude at the beginning of REPL
  (value, st) <- runStateT (runErrorT $ evalStr "(eval* (read* (slurp \"prelude.lsp\")))")
    $ env { traceFlag = True }
  either fail (\_ -> replCont (st { traceFlag = False}) "") value

replCont :: Env -> String -> IO ()
replCont env parsed = do
  putStr $ if length parsed > 0 then ">> " else "> "
  -- three cases: (i) regular line, (ii) continuation line (ending with \) or (iii) REPL command
  line <- getLine
  let text = parsed ++ "\n" ++ line
  if endswith "\\" text then replCont env (init text) else replEval env text

replEval :: Env -> String -> IO ()
replEval env parsed = do
  (vals, st) <- runStateT (runErrorT $ evalStr parsed) env
  either (\x -> putStr "ERROR: " >> putStrLn x) (mapM_ print) vals
  replCont (either (\_ -> st) (\vs -> if length vs > 0 then bindVar st "$" (last vs) else st) vals) ""


-- Some utilities

tryReadFile :: String -> IO String
tryReadFile = readFile
-- tryReadFile n = catch (readFile n)
--                     (\e -> fail "Could not open file " ++ n ++ " due to: " ++ show (e :: IOException))

--
-- primitive functions
-- 

primFuns = [
  "rest", "apply", "print", "eval", "eval*", "slurp", "read*", "macroexpand-1", "macroexpand",
  "cons", "first", "type", "seq?", "seqable?", "container?", "seq", "conj",
  "+", "-", "*", "div", "mod", "<", "=", "list", "count",
  "trace", "fail"]
primSpecials = ["def", "do", "if", "dump", "quote", "unify", "lambda", "macro", "backquote"]

makePrimLambda :: String -> Expr
makePrimLambda name = Fun $ Lambda name ENil ENil $ prim name
makePrimSpecial :: String -> Expr
makePrimSpecial name = ESpecial name $ prim name

-- implementations of both functions and specials
prim :: String -> [Expr] -> Computation

--
-- functions, having parameters passed evaluated
--
prim "rest" (param : _) = return . EList $ rest where
   elems = seqElems param
   rest = if null elems then [] else tail . seqElems $ param
prim "apply" (f : params) = let vals = init params ++ (seqElems $ last params) in
   apply f vals
prim "print" params = (liftIO . putStr . Str.join "" $ map printShow params) >> return ENil
prim "eval" (param : _) = evalExpr param
prim "eval*" (s : _) = do
     values <- (expandProgram (seqElems s) >>= evalProgram)
     return $ if length values == 0 then ENil else last values
prim "slurp" ((EString n) : _) = liftIO $ tryReadFile n >>= return . EString
prim "read*" ((EString s) : _) = readProgram s >>= return . EList
prim "macroexpand-1" (e : _) = expandMacro1 e >>= maybe (return e) return
prim "macroexpand" (e : _) = expandMacro e
prim "cons" (f : s : _) = return $ EList (f : seqElems s)
prim "first" (s : _) = return $ if null elems then ENil else head elems where
  elems = seqElems s
prim "type" (f : _) = return . EString . exprType $ f
prim "seq?" (s : _) = return . EBool $ isSeq s
prim "seqable?" (s : _) = return . EBool $ isSeqable s
prim "container?" (s : _) = return . EBool $ isContainer s
-- NOTE: seq on a map creates a FLAT list of keys and values interleaved!
prim "seq" (s : _) = let elems = seqElems s in
     return $ if null elems then ENil else EList elems
-- conj can add many elements, where maps expects sequences of key and value
-- for each added element
prim "conj" (s : adding) = return $ foldl conj s adding
prim "+" s = numHandler (foldl (+) 0) s
prim "-" s = numHandler (\(n : ns) -> if ns==[] then - n else (foldl (-) n ns)) s
prim "*" s = numHandler (foldl (*) 1) s
prim "div" s = numHandler (foldl1 div) s
prim "mod" s = numHandler (foldl1 mod) s
prim "<" (p1 : p2 : []) = return $ EBool (p1 < p2)
prim "=" (p1 : p2 : []) = return $ EBool (p1 == p2)
prim "list" params = return $ EList params
prim "count" ((EMap m) : _) = return . ENumber . toInteger . M.size $ m
prim "count" (s : _) = return . ENumber . toInteger . length . seqElems $ s
prim "trace" (flag : _) = setTrace (isTruthy flag) >>= return . EBool
prim "fail" args = fail $ Str.join " " $ map show args

--
-- special forms, with parameters unevaluated
--
-- TODO: allow def with zero or more than 1 value arguments
prim "def" [ESymbol var, value] = do
     evalValue <- evalExpr value
     e <- get
     put $ bindVar e var evalValue
     return evalValue
prim "do" params = if null params then return ENil else liftM last . mapM evalExpr $ params
prim "if" (condPart : thenPart : elsePart : []) = do
     cond <- evalExpr condPart
     evalExpr $ if isTruthy cond then thenPart else elsePart
prim "dump" _ = do 
      liftIO $ putStrLn "DUMP: "
      liftIO $ putStrLn "ENV = "
      printComp
      return ENil
prim "quote" (param : _) = do
      return $ param
prim "unify" (formal : actual : []) = unifyState formal actual >>= return . EBool
prim "lambda" (s : body) = do
      let doBody = case body of
                     [b] -> b
                     _ -> (EList (ESymbol "do": body))
      ce <- get
      return $ Fun $ Lambda "lambda" s doBody (\actuals -> do
        e <- get
        setLocalEnv $ localEnv ce
        alright <- unifyState s $ EList actuals
        if alright then return ENil else (throwError $ "Could not bind formal parameters " ++ show s ++ " with actual parameters " ++ show (EList actuals) ++ " for function with body " ++ show body)
        val <- evalExpr doBody
        setLocalEnv $ localEnv e
        return val)
-- TODO: the macro definition is identical to that of "lambda"!
prim "macro" (s : body) = do
      let doBody = case body of
                     [b] -> b
                     _ -> (EList (ESymbol "do": body))
      ce <- get
      return $ Macro $ Lambda "macro" s doBody (\actuals -> do
        e <- get
        setLocalEnv $ localEnv ce
        alright <- unifyState s $ EList actuals
        if alright then return ENil else (throwError $ "Could not bind formal parameters " ++ show s ++ " with actual parameters " ++ show (EList actuals) ++ " for function with body " ++ show body)
        expanded <- evalExpr doBody
        setLocalEnv . localEnv $ e
        return expanded)
prim "backquote" (s : _) = do
  backquote 1 s

prim fun args = fail $ "Got a strange call of " ++ show fun ++ " on " ++ show args


-- Utilities to simplify parsing and evaluating individual expressions

preludeEnv :: IO Env
preludeEnv = do
--  (_, st) <- runStateT (runErrorT $ evalStr "(eval* (read* (slurp \"prelude.lsp\")))") createEmptyEnv
--  return st
  let env = bindVar createEmptyEnv "*prefix-symbols*" $ EList $ map ESymbol ["`", "'", "~", "~@"]
  return $ env { traceFlag = True }

testParseList :: String -> [Expr]
testParseList = either ((:[]) . EString . show) id . parse parseProgram ""

testParse :: String -> Expr
testParse = either (EString .show) id . parse parseExpr ""

testExpand1 :: Expr -> IO Expr
testExpand1 e = do
  env <- preludeEnv
  (val, _) <- runStateT (runErrorT $ expandMacro1 e) env
  return $ either (EString . show) (maybe ENil id) val

testExpand :: Expr -> IO Expr
testExpand e = do
  env <- preludeEnv
  (val, _) <- runStateT (runErrorT $ expandMacro e) env
  return $ either EString id val

testShuffle :: [Expr] -> IO [Expr]
testShuffle e = do
  env <- preludeEnv
  (val, _) <- runStateT (runErrorT $ shufflePrefixList e) env
  return $ either ((:[]) . EString) id val

testEval :: Expr -> IO Expr
testEval e = do
   env <- preludeEnv
   (val, _) <- runStateT (runErrorT $ evalExpr e) env
   return $ either EString id val

-- backquote tracks the nesting level of backquotes, where 1
-- indicates that we are at the top level of a backquoted form,
-- and 0 that we are one unquote down from that, i.e., ready to evaluate

wrapQuote :: Int -> Expr -> Expr
wrapQuote 0 e = e
wrapQuote depth e = EList [(ESymbol "quote"), (wrapQuote (depth - 1) e)]

backquote :: Int -> Expr -> Computation
backquote depth e@(EList [ESymbol "`", expr]) = backquote (depth + 1) expr
backquote 0 e = evalExpr e
backquote depth e@(EList [ESymbol "~", expr]) = backquote (depth - 1) expr
backquote depth e | isSeq e = backquoteList depth (seqElems e) >>= return . makeSeq (seqType e)
                  | True = return $ wrapQuote (depth - 1) e

backquoteList :: Int -> [Expr] -> ComputationM [Expr]
backquoteList depth (EList [ESymbol "~@", expr] : rest) = do
  val <- backquote (depth - 1) expr
  let elems = seqElems val
  valRest <- backquoteList depth rest
  return $ elems ++ valRest
backquoteList depth (f : r) = do
  fval <- backquote depth f
  rval <- backquoteList depth r
  return $ (fval : rval)
backquoteList _ [] = return []


prefixSymbols :: ComputationM [Expr]
prefixSymbols = do
  e <- get
  return $ maybe [] seqElems (getVar e "*prefix-symbols*")

isPrefixSymbol :: Expr -> ComputationM Bool
isPrefixSymbol e = do
  syms <- prefixSymbols
  return $ elem e syms



-- string and char utils

getCharLiteral :: String -> Char
getCharLiteral [c] = c
-- TODO: implement properly
getCharLiteral x = '?'
