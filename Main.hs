module Main where

import Prelude hiding (catch)
import Text.ParserCombinators.Parsec hiding (State)
import Text.ParserCombinators.Parsec.Token as P hiding (operator)
import Text.Parsec.Numbers as Num
import Text.ParserCombinators.Parsec.Char
import Text.Parsec.Language (haskellDef)
import Data.Either
import Data.Maybe
import Data.String.Utils as Str
import Data.List.Utils
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
data Expr = EKeyword String | ESymbol String | EList [Expr] | ENumber Integer |
            EString String | EBool Bool | ENil | Fun Lambda | Macro Lambda | ESpecial String Function
instance Show Expr where
  show (EKeyword s) = ":" ++ s
  show (ESymbol s) = s
  show (EList es) = "(" ++ (Str.join " " $ map show es) ++ ")"
  show (ENumber num) = show num
  show (EString s) = "\"" ++ s ++ "\""
  show (EBool b) = if b then "true" else "false"
  show ENil = "nil"
  show (Fun lambda) = show lambda
  show (Macro lambda) = show lambda
  show (ESpecial s _) = s
instance Eq Expr where
  EKeyword s1 == EKeyword s2 = s1 == s2
  ESymbol s1 == ESymbol s2 = s1 == s2
  EList e1 == EList e2 = all (\(x1, x2) -> x1 == x2) $ zip e1 e2
  ENumber num1 == ENumber num2 = num1 == num2
  EString s1 == EString s2 = s1 == s2
  EBool b1 == EBool b2 = b1 == b2
  ENil == ENil = True
  Fun (Lambda n1 p1 e1 _) == Fun (Lambda n2 p2 e2 _) = n1 == n2 && e1 == e2 && p1 == p2
  ESpecial s1 _ == ESpecial s2 _ = s1 == s2
  _ == _ = False
instance Ord Expr where
  EKeyword s1 < EKeyword s2 = s1 < s2
  ESymbol s1 < ESymbol s2 = s1 < s2
  ENumber s1 < ENumber s2 = s1 < s2
  EString s1 < EString s2 = s1 < s2
  _ < _ = False
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
data Env = Env { globalEnv :: Bindings, localEnv :: Bindings }

trace :: Expr -> IO ()
trace = print

printShow :: Expr -> String
printShow (EString s) = s
printShow x = show x

printEnv :: Env -> IO ()
printEnv (Env global local) = do
  putStrLn "global"
  printBindings global
  putStrLn "local"
  printBindings local

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
getVar (Env global local) var = listToMaybe $ catMaybes [(Map.lookup var local), (Map.lookup var global)]

bindVar :: Env -> String -> Value -> Env
bindVar env@(Env global local) k v = env { globalEnv = Map.insert k v global }

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
createEmptyEnv = Env (createBindings [
  -- specials
  "def", "do", "if", "trace", "quote", "lambda", "macro",
  -- primitives
  "print", "eval", "slurp", "read*", "macroexpand-1",
  "cons", "first", "rest",
  "+", "-", "*", "div", "mod", "<", "=", "list", "nil", "false", "true"]
  [ESpecial "def" (\((ESymbol var):value:[]) -> do
     evalValue <- evalExpr value
     e <- get
     put $ bindVar e var evalValue
     return evalValue),
   ESpecial "do" (\params -> liftM last (mapM evalExpr params)),
   ESpecial "if" (\(condPart : thenPart : elsePart : []) -> do
     cond <- evalExpr condPart
     evalExpr (if (isTruthy cond) then thenPart else elsePart)),
   ESpecial "trace" (\(param : []) -> do 
      liftIO $ putStrLn "TRACE: "
      liftIO $ putStrLn "ENV = "
      printComp
      liftIO $ putStr "\nEXP = "
      liftIO $ trace param
      liftIO $ putStr "\nVAL = "
      evalParam <- evalExpr param
      liftIO $ trace evalParam
      liftIO $ putStrLn ""
      return evalParam),
   ESpecial "quote" (\(param : _) -> do
      return $ param),
   ESpecial "lambda" (\((EList params) : body) -> do
      let doBody = (EList ((ESymbol "do") : body))
      return $ Fun $ Lambda "lambda" params doBody (\actuals -> do
        e <- get
        let local = localEnv e
        let params' = map ((fromMaybe "_") . name) params
        let e' = combineEnv e (createBindings params' actuals)
        put e'
        val <- evalExpr doBody
        setLocalEnv local        
        return val)),
   ESpecial "macro" (\((EList params) : body) -> do
      let doBody = (EList ((ESymbol "do") : body))
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
   Fun (Lambda "slurp" [] ENil $ (\((EString n) : _) -> do
     cont <- liftIO $ tryReadFile n
     return $ EString cont
   )),
   Fun (Lambda "read*" [] ENil $ (\((EString s) : _) -> do
     let exprs = readProgram s
     either (\e -> throwError $ "Could not read code due to " ++ show e) (return . EList) exprs
   )),
   Fun (Lambda "macroexpand-1" [] ENil $ (\((EList (m : params) : _)) -> do
     macro <- evalExpr m
     apply macro params)),
   Fun (Lambda "cons" [] ENil $ (\(f : (EList r) : _) -> return $ EList (f : r))),
   Fun (Lambda "first" [] ENil $ (\((EList (f: _)) : _) -> return f)),
   Fun (Lambda "rest" [] ENil $ (\((EList (_: r)) : _) -> return $ EList r)),
   Fun (Lambda "+" [] ENil $ numHandler (foldl1 (+))),
   Fun (Lambda "-" [] ENil $ numHandler (\(n : ns) -> if ns==[] then - n else (foldl (-) n ns))),
   Fun (Lambda "*" [] ENil $ numHandler (foldl1 (*))),
   Fun (Lambda "div" [] ENil $ numHandler (foldl1 div)),
   Fun (Lambda "mod" [] ENil $ numHandler (foldl1 mod)),
   Fun (Lambda "<" [] ENil $ (\(p1 : p2 : []) -> return $ EBool (p1 < p2))),
   Fun (Lambda "=" [] ENil $ (\(p1 : p2 : []) -> return $ EBool (p1 == p2))),
   Fun (Lambda "list" [] ENil $ (\params -> return $ EList params)),
   ENil,
   EBool False,
   EBool True])
   createEmptyBindings

createEmptyState :: Computation
createEmptyState = put createEmptyEnv >> return ENil

combineEnv :: Env -> Bindings -> Env
combineEnv env@(Env global local) bindings = env { localEnv = Map.union local bindings }

--
-- The parser, using Parsec
--

lexer = P.makeTokenParser haskellDef
operator = oneOf "!#$%&|*+-/:<=>?_'"
parseProgram = many parseSpacedExpr
parseSpacedExpr = skipMany space >> parseExpr
parseString = do char '"'
                 str <- many $ noneOf "\""
                 char '"'
                 return $ EString str
parseNumber =  do
  num <- try Num.parseIntegral
  return $ ENumber num
parseKeyword = do char ':'
                  atom <- many (letter <|> digit <|> operator)
                  return $ EKeyword atom
parseSymbol = do  f <- letter <|> operator
                  r <- many (letter <|> digit <|> operator)
                  let atom = f:r
                  return $ ESymbol atom
parseAtom =  parseNumber <|> parseString <|> parseKeyword <|> parseSymbol
parseList = P.parens lexer $ liftM EList $ sepBy parseExpr spaces
parseExpr = parseAtom <|> parseList

readProgram :: String -> ParseResult
readProgram input = either (Left . show) Right $ parse parseProgram "clojure" input
readExpr :: String -> ParseResult
readExpr input = either (Left . show) (Right . (\x -> [x])) $ parse parseExpr "clojure" input

--
-- Evaluator, yielding (and executing...) a computation
--

evalProgram :: [Expr] -> ComputationM [Value]
evalProgram exprs = mapM evalExpr exprs

evalExpr :: Expr -> Computation
evalExpr (EKeyword key) = return (EKeyword key)
evalExpr (ESymbol sym) = do env <- get
                            let value = getVar env sym
                            maybe (throwError $ "Symbol " ++ sym ++ " had no value") return value
evalExpr (EList []) = return $ EList []
evalExpr (EList (f : params)) = do
  fun <- evalExpr f
  apply fun params
evalExpr e@(ENumber n) = return e
evalExpr e@(EString s) = return e
evalExpr e@(Fun f) = return e
evalExpr e@(ESpecial n s) = return e
evalExpr e@(Macro f) = return e

evalExpr expr = throwError $ "Could not evaluate " ++ show expr

evalStr :: String -> ComputationM [Value]
evalStr s = either (\e -> throwError e) evalProgram $ readProgram s

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

expandMacro (Macro (Lambda _ _ _ f)) params = f params
expandMacro f params = return $ EList params

main :: IO ()
main = repl createEmptyEnv

repl :: Env -> IO ()
repl env = replCont env ""

replCont :: Env -> String -> IO ()
replCont env parsed = do
  putStr $ if length parsed > 0 then ">> " else "> "
  -- three cases: (i) regular line, (ii) continuation line (ending with \) or (iii) REPL command
  line <- getLine
  let text = parsed ++ line
  if endswith "\\" text then replCont env (init text) else replEval env text

replEval :: Env -> String -> IO ()
replEval env parsed = do
  (vals, st) <- runStateT (runErrorT $ evalStr parsed) env
  either (\x -> putStr "ERROR: " >> putStrLn x) (mapM_ print) vals
  repl $ either (\_ -> st) (\vs -> if length vs > 0 then bindVar st "$" (last vs) else st) vals


-- Some utilities

tryReadFile :: String -> IO String
tryReadFile = readFile
-- tryReadFile n = catch (readFile n)
--                     (\e -> fail "Could not open file " ++ n ++ " due to: " ++ show (e :: IOException))
