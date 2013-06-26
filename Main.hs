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
  show (Lambda name params expr _) = name ++ "[\\" ++ show params ++ " --> " ++ show expr ++ "]"
type Param = Expr
data SeqType = SeqList | SeqVector | SeqMap | SeqSet deriving (Show, Read, Eq, Ord)
leftDelim SeqList = "("
leftDelim SeqVector = "["
leftDelim SeqSet = "#{"
leftDelim SeqMap = "{"
rightDelim SeqList = ")"
rightDelim SeqVector = "]"
rightDelim SeqSet = "}"
rightDelim SeqMap = "}"

isSeq :: Expr -> Bool
isSeq (EList _) = True
isSeq (EVector _) = True
isSeq (ESet _) = True
isSeq (EMap _) = True
isSeq (EString _) = True
isSeq _ = False

seqType (EList _) = SeqList
seqType (EVector _) = SeqVector
seqType (ESet _) = SeqSet
seqType (EMap _) = SeqMap

seqElems :: Expr -> [Expr]
seqElems (EList es) = es
seqElems (EVector es) = es
seqElems (ESet s) = S.elems s
-- NOTE: the sequence from a map is actually a flat list with every odd element key and
-- even element value
seqElems (EMap m) = M.elems m
seqElems (EString s) = map (\c -> EString [c]) s
seqElems x = []

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (a : b : r) = (a,b) : pairs r
pairs [a] = [(a,a)]

makeSeq :: SeqType -> [Expr] -> Expr
makeSeq SeqList = EList
makeSeq SeqSet = ESet . S.fromList
makeSeq SeqVector = EVector
-- NOTE: the sequence to a map is actually a flat list with every odd element key and even value
makeSeq SeqMap = EMap . M.fromList . pairs

conj :: Expr -> Expr -> Expr
conj (EList s) e = EList (e:s)
conj (EVector s) e = EVector $ s ++ [e] -- NOTE: quite inefficient!
-- NOTE: conj:ing to a map requires a seqable element with at least two
-- elements, being the new key and value to be added
conj (EMap m) e = let (k:v:_) = seqElems e in EMap $ M.insert k v m
conj (ESet s) e = ESet $ S.insert e s

data Expr = EKeyword String (Maybe String) | ESymbol String | ENumber Integer |
            EString String | EBool Bool | ENil | Fun Lambda | Macro Lambda | ESpecial String Function | EList [Expr] | EVector [Expr] | ESet (S.Set Expr) | EMap (M.Map Expr Expr)
instance Show Expr where
  show (EKeyword s Nothing) = ":" ++ s
  show (EKeyword s (Just ns)) = ":" ++ ns ++ "/" ++ s
  show (ESymbol s) = s
  show (EString s) = "\"" ++ s ++ "\""
  show (ENumber num) = show num
  show (EBool b) = if b then "true" else "false"
  show ENil = "nil"
  show (Fun lambda) = show lambda
  show (Macro lambda) = show lambda
  show (ESpecial s _) = s
  show (EMap m) = "{ " ++ Str.join ", " (map (\(k,v) -> show k ++ ": " ++ show v) $ M.assocs m) ++ " }"
  show e | isSeq e = leftDelim (seqType e) ++ (Str.join " " $ map show elems) ++ rightDelim (seqType e) where
    elems = seqElems e
instance Eq Expr where
  EKeyword ns1 s1 == EKeyword ns2 s2 = ns1 == ns2 && s1 == s2
  ESymbol s1 == ESymbol s2 = s1 == s2 
  ENumber num1 == ENumber num2 = num1 == num2
  EString s1 == EString s2 = s1 == s2
  EBool b1 == EBool b2 = b1 == b2
  ENil == ENil = True
  Fun (Lambda n1 p1 e1 _) == Fun (Lambda n2 p2 e2 _) = n1 == n2 && e1 == e2 && p1 == p2
  ESpecial s1 _ == ESpecial s2 _ = s1 == s2
  seq1 == seq2 | isSeq seq1 && isSeq seq2 =
    seqType seq1 == seqType seq2 && seqElems seq1 == seqElems seq2
  _ == _ = False
lexico comps = if length diffs == 0 then EQ else head diffs where diffs = filter (/= EQ) comps
instance Ord Expr where
  EKeyword ns1 s1 `compare` EKeyword ns2 s2 = lexico [ns1 `compare` ns2, s1 `compare` s2]
  ESymbol s1 `compare` ESymbol s2 = s1 `compare` s2
  ENumber s1 `compare` ENumber s2 = s1 `compare` s2
  EString s1 `compare` EString s2 = s1 `compare` s2
  seq1 `compare` seq2 | isSeq seq1 && isSeq seq2 =
    (seqType seq1, seqElems seq1) `compare` (seqType seq2, seqElems seq2)
  e1 `compare` e2 = show e1 `compare` show e2
type ParseResult = Either Err [Expr]

exprType :: Expr -> String
exprType (Fun {}) = "fun"
exprType (EKeyword {}) = "keyword"
exprType (ENumber {}) = "number"
exprType (ESymbol {}) = "symbol"
exprType (EString {}) = "string"
exprType (ENil {}) = "nil"
exprType (ESpecial {}) = "special"
exprType e | isSeq e = "seq"

--
-- Environment
--
-- Has a global binding and a local binding
--

-- Expressions evaluate to Herbrand values
type Value = Expr

-- The computation monad has to handle
type Bindings = Map.Map String Value
data Env = Env { globalEnv :: Bindings, localEnv :: Bindings, traceFlag :: Bool }

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
unify s1 s2 b | isSeq s1 && isSeq s2 = unifyList (seqElems s1) (seqElems s2) b
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
createEmptyEnv = Env { traceFlag = False, globalEnv = createBindings [
  -- specials
  "def", "do", "if", "dump", "quote", "unify", "lambda", "macro",
  -- primitives
  "apply", "print", "eval", "eval*", "slurp", "read*", "macroexpand-1", "macroexpand",
  "cons", "first", "rest", "type", "seq?", "seq", "conj",
  "+", "-", "*", "div", "mod", "<", "=", "list", "nil", "false", "true",
  "trace"]
  [ESpecial "def" (\((ESymbol var):value:[]) -> do
     evalValue <- evalExpr value
     e <- get
     put $ bindVar e var evalValue
     return evalValue),
   ESpecial "do" (\params -> liftM last (mapM evalExpr params)),
   ESpecial "if" (\(condPart : thenPart : elsePart : []) -> do
     cond <- evalExpr condPart
     evalExpr (if (isTruthy cond) then thenPart else elsePart)),
   ESpecial "dump" (\_ -> do 
      liftIO $ putStrLn "DUMP: "
      liftIO $ putStrLn "ENV = "
      printComp
      return ENil),
   ESpecial "quote" (\(param : _) -> do
      return $ param),
   ESpecial "unify" (\(formal : actual : body) -> do
      let doBody = (EList (ESymbol "do" : body))
      ok <- unifyState formal actual
      if ok then evalExpr doBody else return ENil
      ),
   ESpecial "lambda" (\(s : body) -> do
      let doBody = (EList (ESymbol "do" : body))
      ce <- get
      return $ Fun $ Lambda "lambda" s doBody (\actuals -> do
        e <- get
        setLocalEnv $ localEnv ce
        alright <- unifyState s $ EList actuals
        if alright then return ENil else (throwError $ "Could not bind parameters in " ++ show body)
        val <- evalExpr doBody
        setLocalEnv $ localEnv e
        return val)),
   ESpecial "macro" (\(s : body) -> do
      let doBody = (EList (ESymbol "do": body))
      ce <- get
      return $ Macro $ Lambda "macro" s doBody (\actuals -> do
        e <- get
        setLocalEnv $ localEnv ce
        alright <- unifyState s $ EList actuals
        if alright then return ENil else (throwError $ "Could not bind parameters in " ++ show body)
        expanded <- evalExpr doBody
        setLocalEnv . localEnv $ e
        return expanded)),
   Fun (Lambda "apply" (EList [ESymbol "f", ESymbol "args..."]) ENil (\(f : params) ->
      let vals = init params ++ (seqElems $ last params) in
      apply f vals)),
   Fun (Lambda "print" (EList [ESymbol "args..."]) ENil (\params -> do
      liftIO . putStr . Str.join "" $ map printShow params
      return ENil)),
   Fun (Lambda "eval" (EList [ESymbol "form"]) ENil $ (\(param : _) ->
     evalExpr param
   )),
   Fun (Lambda "eval*" (EList [ESymbol "forms"]) ENil $ (\(s : _) -> do
     let exprs = seqElems s
     values <- mapM evalExpr exprs
     return $ if length values == 0 then ENil else last values
   )),
   Fun (Lambda "slurp" (EList [ESymbol "path"]) ENil $ (\((EString n) : _) -> do
     cont <- liftIO $ tryReadFile n
     return $ EString cont
   )),
   Fun (Lambda "read*" (EList [ESymbol "text"]) ENil $ (\((EString s) : _) -> do
     readProgram s >>= return . EList
   )),
   Fun (Lambda "macroexpand-1" (EList [ESymbol "form"]) ENil $ (\(e : _) ->
     expandMacro1 e)),
   Fun (Lambda "macroexpand" (EList [ESymbol "form"]) ENil $ (\(e : _) ->
     expandMacro e)),
   Fun (Lambda "cons" (EList [ESymbol "elem", ESymbol "seq"]) ENil $ (\(f : s : _) -> return $ EList (f : seqElems s))),
   Fun (Lambda "first" (EList [ESymbol "seq"]) ENil $ (\(s : _) -> return . head . seqElems $ s)),
   Fun (Lambda "rest" (EList [ESymbol "seq"]) ENil $ (\(s : _) -> return . EList . tail . seqElems $ s)),
   Fun (Lambda "type" (EList [ESymbol "x"]) ENil $ (\(f : _) -> return . EString . exprType $ f)),
   Fun (Lambda "seq?" (EList [ESymbol "x"]) ENil $ (\(s : _) -> return . EBool $ isSeq s)),
   -- NOTE: seq on a map creates a FLAT list of keys and values interleaved!
   Fun (Lambda "seq" (EList [ESymbol "seq"]) ENil $ (\(s : _) ->
     let elems = (if isSeq s then seqElems s else []) in return $
     if null elems then ENil else EList elems)),
   -- conj can add many elements, where maps expects sequences of key and value
   -- for each added element
   Fun (Lambda "conj" (EList [ESymbol "seq", ESymbol "elem"]) ENil $ (\(s : adding) -> return $ foldl conj s adding)),
   Fun (Lambda "+" (EList [ESymbol "nums..."]) ENil $ numHandler (foldl (+) 0)),
   Fun (Lambda "-" (EList [ESymbol "nums..."]) ENil $ numHandler (\(n : ns) -> if ns==[] then - n else (foldl (-) n ns))),
   Fun (Lambda "*" (EList [ESymbol "nums..."]) ENil $ numHandler (foldl (*) 1)),
   Fun (Lambda "div" (EList [ESymbol "nums..."]) ENil $ numHandler (foldl1 div)),
   Fun (Lambda "mod" (EList [ESymbol "num1", ESymbol "num2"]) ENil $ numHandler (foldl1 mod)),
   Fun (Lambda "<" (EList [ESymbol "x1", ESymbol "x2"]) ENil $ (\(p1 : p2 : []) -> return $ EBool (p1 < p2))),
   Fun (Lambda "=" (EList [ESymbol "x1", ESymbol "x2"]) ENil $ (\(p1 : p2 : []) -> return $ EBool (p1 == p2))),
   Fun (Lambda "list" (EList [ESymbol "elems..."]) ENil $ (\params -> return $ EList params)),
   ENil,
   EBool False,
   EBool True,
   Fun (Lambda "trace" (EList [ESymbol "flag"]) ENil $ (\(flag : _) ->
     (setTrace $ isTruthy flag) >>= return . EBool))],
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
    opStart = oneOf "~#",
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
parseString = EString <$> P.stringLiteral lexer <?> "string"
parseNumber =  ENumber <$> (try . lex) Num.parseIntegral <?> "number"
parseKeyword = flipNs .* EKeyword <$>
               lex (char ':' *>
                P.identifier lexer) <*>
               optionMaybe (char '/' *> ident)
               <?> "keyword"
parseSymbol = ESymbol <$> lex (ident <|> oper)
              <?> "symbol"
parseAtom =  choice [parseNumber, parseString, parseKeyword, parseSymbol]
             <?> "atom"
parseSeq seqType = makeSeq seqType <$> 
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

expandProgram :: [Expr] -> ComputationM [Expr]
expandProgram exprs = mapM expandMacro exprs

readProgram :: String -> ComputationM [Expr]
readProgram text = either throwError  expandProgram $ parseProgramText text

--
-- Evaluator, yielding (and executing...) a computation
--

evalProgram :: [Expr] -> ComputationM [Value]
evalProgram exprs = mapM evalExpr exprs

evalExpr :: Expr -> Computation
evalExpr e@(EKeyword _ _) = return e
evalExpr (ESymbol sym) = do env <- get
                            let value = getVar env sym
                            maybe (throwError $ "Symbol " ++ sym ++ " had no value") return value
evalExpr (EList (f : params)) = do
  fun <- evalExpr f
  apply fun params
evalExpr e@(ENumber n) = return e
evalExpr e@(EString s) = return e
evalExpr e@(Fun f) = return e
evalExpr e@(ESpecial n s) = return e
evalExpr e@(Macro f) = return e
evalExpr e@ENil = return e
evalExpr e | isSeq e = do
  vals <- mapM evalExpr $ seqElems e
  return $ makeSeq (seqType e) vals
evalExpr expr = throwError $ "Could not evaluate " ++ show expr

-- evalStr evalues expression by expression, thus allowing for definitions
-- of reader macros
evalStr :: String -> ComputationM [Value]
evalStr s = readProgram s >>= evalProgram

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
apply other _ = throwError $ "Cannot apply as a function: " ++ show other

isMacro :: Expr -> Bool
isMacro (Macro _) = True
isMacro _ = False

expandMacro1 :: Expr -> Computation
expandMacro1 e@(EList ((Macro (Lambda n _ _ f)) : params)) =
  f params
expandMacro1 e@(EList (f : params)) = do
  env <- get
  (fval, newSt) <- lift $ lift $ runStateT (runErrorT $ evalExpr f) env
  put newSt
  either (\err -> return e) (\val -> if val == f || not (isMacro val) then return e else expandMacro1 (EList (val : params))) fval
expandMacro1 e = return e

expandMacro :: Expr -> Computation
expandMacro e = do
  exp <- expandMacro1 e
  printTrace $ "Expanded one step, from " ++ show e ++ " to " ++ show exp
  if exp == e then return exp else expandMacro exp

main :: IO ()
main = repl createEmptyEnv

repl :: Env -> IO ()
repl env = do
  -- we emulate a loading of the prelude at the beginning of REPL
  (value, st) <- runStateT (runErrorT $ evalStr "(eval* (read* (slurp \"prelude.lsp\")))") env
  replCont st ""

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
