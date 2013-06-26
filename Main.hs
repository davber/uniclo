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
data Lambda = Lambda String [Param] Expr Function
instance Show Lambda where
  show (Lambda name params expr _) = name ++ "[" ++ show expr ++ "]"
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

data Expr = EKeyword String (Maybe String) | ESymbol String | ESeq SeqType [Expr] | ENumber Integer |
            EString String | EBool Bool | ENil | Fun Lambda | Macro Lambda | ESpecial String Function
instance Show Expr where
  show (EKeyword s Nothing) = ":" ++ s
  show (EKeyword s (Just ns)) = ":" ++ ns ++ "/" ++ s
  show (ESymbol s) = s
  show (ESeq seqType es) = leftDelim seqType ++ (Str.join " " $ map show es) ++ rightDelim seqType
  show (ENumber num) = show num
  show (EString s) = "\"" ++ s ++ "\""
  show (EBool b) = if b then "true" else "false"
  show ENil = "nil"
  show (Fun lambda) = show lambda
  show (Macro lambda) = show lambda
  show (ESpecial s _) = s
instance Eq Expr where
  EKeyword ns1 s1 == EKeyword ns2 s2 = ns1 == ns2 && s1 == s2
  ESymbol s1 == ESymbol s2 = s1 == s2
  ESeq st1 e1 == ESeq st2 e2 = st1 == st2 &&
    all (\(x1, x2) -> x1 == x2) (zip e1 e2)
  ENumber num1 == ENumber num2 = num1 == num2
  EString s1 == EString s2 = s1 == s2
  EBool b1 == EBool b2 = b1 == b2
  ENil == ENil = True
  Fun (Lambda n1 p1 e1 _) == Fun (Lambda n2 p2 e2 _) = n1 == n2 && e1 == e2 && p1 == p2
  ESpecial s1 _ == ESpecial s2 _ = s1 == s2
  _ == _ = False
lexico comps = if length diffs == 0 then EQ else head diffs where diffs = filter (/= EQ) comps
instance Ord Expr where
  EKeyword ns1 s1 `compare` EKeyword ns2 s2 = lexico [ns1 `compare` ns2, s1 `compare` s2]
  ESymbol s1 `compare` ESymbol s2 = s1 `compare` s2
  ENumber s1 `compare` ENumber s2 = s1 `compare` s2
  EString s1 `compare` EString s2 = s1 `compare` s2
  ESeq st1 elems1 `compare` ESeq st2 elems2
    | st1 == st2 = lexico $ zipWith compare elems1 elems2 ++ [length elems1 `compare` length elems2]
    | True = st1 `compare` st2
  e1 `compare` e2 = show e1 `compare` show e2
type ParseResult = Either Err [Expr]

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
  "def", "do", "if", "dump", "quote", "lambda", "macro",
  -- primitives
  "print", "eval", "eval*", "slurp", "read*", "macroexpand-1", "macroexpand",
  "cons", "first", "rest",
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
   ESpecial "lambda" (\((ESeq _ params) : body) -> do
      let doBody = (ESeq SeqList ((ESymbol "do") : body))
      return $ Fun $ Lambda "lambda" params doBody (\actuals -> do
        e <- get
        let local = localEnv e
        let params' = map ((fromMaybe "_") . name) params
        let e' = combineEnv e (createBindings params' actuals)
        put e'
        val <- evalExpr doBody
        setLocalEnv local        
        return val)),
   ESpecial "macro" (\((ESeq _ params) : body) -> do
      let doBody = (ESeq SeqList ((ESymbol "do") : body))
      return $ Macro $ Lambda "macro" params doBody (\actuals -> do
        e <- get
        let local = localEnv e
        let params' = map ((fromMaybe "_") . name) params
        let e' = combineEnv e (createBindings params' actuals)
        put e'
        expanded <- evalExpr doBody
        setLocalEnv local
        return expanded)),
   Fun (Lambda "print" [] ENil (\params -> do
      liftIO $ putStr $ Str.join "" $ map printShow params
      return ENil)),
   Fun (Lambda "eval" [] ENil $ (\(param : _) ->
     evalExpr param
   )),
   Fun (Lambda "eval*" [] ENil $ (\((ESeq _ exprs) : _) -> do
     values <- mapM evalExpr exprs
     return $ if length values == 0 then ENil else last values
   )),
   Fun (Lambda "slurp" [] ENil $ (\((EString n) : _) -> do
     cont <- liftIO $ tryReadFile n
     return $ EString cont
   )),
   Fun (Lambda "read*" [] ENil $ (\((EString s) : _) -> do
     readProgram s >>= return . ESeq SeqList
   )),
   Fun (Lambda "macroexpand-1" [] ENil $ (\(e : _) ->
     expandMacro1 e)),
   Fun (Lambda "macroexpand" [] ENil $ (\(e : _) ->
     expandMacro e)),
   Fun (Lambda "cons" [] ENil $ (\(f : (ESeq _ r) : _) -> return $ ESeq SeqList (f : r))),
   Fun (Lambda "first" [] ENil $ (\((ESeq _ (f: _)) : _) -> return f)),
   Fun (Lambda "rest" [] ENil $ (\((ESeq seqType (_: r)) : _) -> return $ ESeq seqType r)),
   Fun (Lambda "+" [] ENil $ numHandler (foldl (+) 0)),
   Fun (Lambda "-" [] ENil $ numHandler (\(n : ns) -> if ns==[] then - n else (foldl (-) n ns))),
   Fun (Lambda "*" [] ENil $ numHandler (foldl (*) 1)),
   Fun (Lambda "div" [] ENil $ numHandler (foldl1 div)),
   Fun (Lambda "mod" [] ENil $ numHandler (foldl1 mod)),
   Fun (Lambda "<" [] ENil $ (\(p1 : p2 : []) -> return $ EBool (p1 < p2))),
   Fun (Lambda "=" [] ENil $ (\(p1 : p2 : []) -> return $ EBool (p1 == p2))),
   Fun (Lambda "list" [] ENil $ (\params -> return $ ESeq SeqList params)),
   ENil,
   EBool False,
   EBool True,
   Fun (Lambda "trace" [] ENil $ (\(flag : _) ->
     (setTrace $ isTruthy flag) >>= return . EBool))],
   localEnv = createEmptyBindings }

-- utility to compose an unary function with a binary one
(.*) = (.) . (.)

createEmptyState :: Computation
createEmptyState = put createEmptyEnv >> return ENil

combineEnv :: Env -> Bindings -> Env
combineEnv e bindings = e { localEnv = Map.union bindings $ localEnv e }

flipNs (EKeyword ns (Just s)) = EKeyword s (Just ns)
flipNs x = x

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
    identStart = oneOf "!#$%&|*+-/<=>?_" <|> letter,
    identLetter = oneOf "!#$%&|*+-<=>?_'" <|> alphaNum,
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
parseSeq seqType = ESeq seqType <$> 
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
evalExpr e@(ESeq _ []) = return e
evalExpr (ESeq SeqList (f : params)) = do
  fun <- evalExpr f
  apply fun params
evalExpr (ESeq SeqSet exprs) = do
  vals <- mapM evalExpr exprs
  return $ ESeq SeqSet $ (S.toList . S.fromList) vals
evalExpr (ESeq seqType exprs) = do
  vals <- mapM evalExpr exprs
  return $ ESeq seqType vals
evalExpr e@(ENumber n) = return e
evalExpr e@(EString s) = return e
evalExpr e@(Fun f) = return e
evalExpr e@(ESpecial n s) = return e
evalExpr e@(Macro f) = return e
evalExpr e@ENil = return e

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
expandMacro1 e@(ESeq SeqList ((Macro (Lambda n _ _ f)) : params)) =
  f params
expandMacro1 e@(ESeq SeqList (f : params)) = do
  env <- get
  (fval, newSt) <- lift $ lift $ runStateT (runErrorT $ evalExpr f) env
  put newSt
  either (\err -> return e) (\val -> if val == f || not (isMacro val) then return e else expandMacro1 (ESeq SeqList (val : params))) fval
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
