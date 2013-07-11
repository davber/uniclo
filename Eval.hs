{-# LANGUAGE Rank2Types #-}
module Eval where

import Control.Monad.Error
import Control.Monad.State
import Control.Exception
import qualified Data.String.Utils as Str
import qualified Data.Map as M
import Data.Char

import Expr
import Common
import Parse
import qualified CompState as S
import Comp

--
-- Environment
--
-- Has a global binding and a local binding
--

-- Computations can either (i) yield a value or (ii) yield an error
-- AND can also interact with the environment
-- We encapsulate this by a three-layer monadic pie:
-- Error - State - IO

-- Try unification, yielding a flag if bindings were created
unifyState :: Expr -> Expr -> Comp Bool
unifyState e1 e2 = do
  let (bindings, flag) = maybe ([], False) (\bindings -> (bindings, True)) $ unifyBindings e1 e2
  printTrace $ "Unification: " ++ show e1 ++ " <|> " ++ show e2 ++ " ==> " ++
               if flag then show bindings else "failed!" 
  addLocalBindings bindings
  return flag

-- Unify two terms, having the latest bindings at the front of the list
unifyBindings :: Expr -> Expr -> Maybe (BindingList)
unifyBindings e1 e2 = unify e1 e2 []

-- Unify two tems, with bindings to the left, adding to the existing
-- binding list
unify :: Expr -> Expr -> BindingList -> Maybe (BindingList)
unify (ESymbol name) value b = Just $ (name, value) : b
unify (EList [ESymbol q, e1]) e2 b | elem q ["'", "quote", "`", "backquote"] =
  if e1 == e2 then Just b else Nothing
unify s1 s2 b | isSeqable s1 && isSeqable s2 = unifyList (seqElems s1) (seqElems s2) b
unify s1 s2 b | s1 == s2 = Just b
              | True = Nothing

unifyList :: [Expr] -> [Expr] -> BindingList -> Maybe BindingList
unifyList [] [] = return
unifyList (ESymbol "&" : rest : _) other = unify rest (EList other)
unifyList (f1:r1) (f2:r2) = (\b -> unify f1 f2 b >>= unifyList r1 r2)
unifyList _ _ = (\_ -> Nothing)

-- applies macro expansion to a program
expandProgram :: [Expr] -> Comp [Expr]
expandProgram exprs = printTrace "*** Expanding program ***" >> mapM (\e -> expandMacro e >>= evalMacro) exprs
-- reading a program both parses and read-expands it
readProgram :: String -> Comp [Expr]
readProgram text = do
  printTrace "*** Parsing program ***"
  either throwError (\expr -> printTrace "*** Reading program ***" >>
                              shufflePrefixList expr >>=
                              shuffleInfixList True) $
                    parseProgramText text

--
-- Evaluator, yielding (and executing...) a computation
--

evalProgram :: [Expr] -> Comp [Expr]
evalProgram exprs = printTrace "*** Evaluating program ***" >> mapM evalExpr exprs

evalExpr :: Expr -> Comp (Expr)
evalExpr e@(EKeyword {}) = return e
evalExpr e@(EChar {}) = return e
evalExpr (ESymbol sym) = getVar sym >>=
  maybe (fail $ "Could not find variable " ++ sym) return
evalExpr e@(EList (f : params)) = do
  fun <- evalExpr f
  res <- case fun of
    Fun { } -> apply fun params
    _ -> fail $ "Cannot apply function " ++ show fun
  -- If the function was an expanding one, we need to here
  -- (re-)evaluate the yielded expression here.
  -- NOTE: this only makes sense during runtime.
  res' <- (if funExpressive (funType fun) then evalExpr else return) res
  printTrace $ "Reduction: " ++ show e ++ " ==> " ++ show res'
  return res'
evalExpr e@(ENumber {}) = return e
evalExpr e@(EString {}) = return e
evalExpr e@(Fun {}) = return e
evalExpr e@(EBool {}) = return e
evalExpr e@ENil = return e
evalExpr e | isSeqable e = do
  vals <- mapM evalExpr $ seqElems e
  return $ makeSeq (seqType e) vals
evalExpr expr = throwError $ "Could not evaluate " ++ show expr ++ " of type " ++ exprType expr

-- evalStr evalues expression by expression, thus allowing for definitions
-- of reader macros
evalStr :: String -> Comp [Expr]
evalStr s = readProgram s >>= expandProgram >>= evalProgram

num :: Expr -> Comp Integer
num (ENumber numb) = return numb
num (EChar c) = return . toInteger . ord $ c
num e = fail $ show e ++ " is not a number"

toChar :: Expr -> Comp Expr
toChar (EString (c:_)) = return . EChar $ c
toChar e@(EChar {}) = return e
toChar (ENumber num) = return . EChar . chr . fromInteger $ num
toChar e = fail $ "Cannot convert to char: " ++ show e

apply :: Expr -> [Expr] -> Comp (Expr)
--
-- When applying a function, we check whether it is call-by-name, in which
-- case we avoid evaluating parameters.
-- NOTE: we assume this can be used during either expansion or runtime phase
--
apply (Fun { funFun = (Just f), funType = fType }) params =
  -- we only evaluate parameters for call-by-value functions
  mapM (if funByName fType then return else evalExpr) params >>= f
apply other args = throwError $ "Not a proper function application: " ++ show (EList (other : args))

--
-- Reader prefix reshuffling, which makes prefix symbols regular prefix forms
-- NOTE: we only care about definitions of the *prefix-symbols* forms for controlling
-- these prefix symbols!
--

shufflePrefix :: Expr -> Comp (Expr)
shufflePrefix defE@(EList [ESymbol "def", ESymbol fixSymbols, expr]) | elem fixSymbols ["*prefix-symbols*", "*infix-symbols*"] = do
  val <- evalExpr expr -- NOTE: usually a literal sequence
  setGlobal $ (fixSymbols, val)
  printTrace $ "Set prefix symbols to " ++ show val
  return defE
shufflePrefix (EList [ESymbol "def", sym, expr]) = do
  expr' <- shufflePrefix expr
  return . EList $ [ESymbol "def", sym, expr']
shufflePrefix e | isContainer e = do
  let elems = seqElems e
  shufflePrefixList elems >>= return . makeSeq (seqType e)
-- TODO: should we not recurse into other conglomerates?
shufflePrefix x = return x

shufflePrefixList :: [Expr] -> Comp [Expr]
-- whenever a prefix symbol is followed by enother one, we deal with it right-associatively
shufflePrefixList e@(first : rest) = do
  shuffleF <- shufflePrefix first
  shuffleR <- shufflePrefixList rest
  isPrefix <- isPrefixSymbol first
  let e' =  if isPrefix && not (null shuffleR)
            then EList [first, head shuffleR] : tail shuffleR
            else shuffleF : shuffleR
  if isPrefix then printTrace $ "Reader (prefix): " ++ show e ++ " ==> " ++ show e' else return ()
  return e'
shufflePrefixList [] = return []

shuffleInfix :: Expr -> Comp Expr
shuffleInfix (EList [ESymbol "def", sym, expr]) = do
  expr' <- shuffleInfix expr
  return . EList $ [ESymbol "def", sym, expr']
shuffleInfix e@(EList es@[arg1, infixS, arg2]) = do
  isInfix <- isInfixSymbol infixS
  if isInfix then do
    a1 <- shuffleInfix arg1
    a2 <- shuffleInfix arg2
    let e' = EList $ [infixS, a1, a2]
    printTrace $ "Reader (infix): " ++ show e ++ " ==> " ++ show e'
    return e'
  else
    liftM EList $ shuffleInfixList True es
shuffleInfix e | isContainer e = do
  let elems = seqElems e
  shuffleInfixList True elems >>= return . makeSeq (seqType e)
shuffleInfix e = return e

shuffleInfixList :: Bool -> [Expr] -> Comp [Expr]
shuffleInfixList shouldShuffleFirst e@(f : e2@(infixS : s : rest)) = do
  isInfix <- isInfixSymbol infixS
  arg1 <- if shouldShuffleFirst then shuffleInfix f else return f
  if isInfix then do
    arg2 <- shuffleInfix s
    e' <- shuffleInfixList False $ EList [infixS, arg1, arg2] : rest
    printTrace $ "Reader (infix): " ++ show e ++ " ==> " ++ show e'
    return e'
  else do
    restE <- shuffleInfixList True e2
    return $ arg1 : restE
shuffleInfixList _ [] = return []
shuffleInfixList shouldShuffleFirst (f : r) = do
  f' <- if shouldShuffleFirst then shuffleInfix f else return f
  r' <- shuffleInfixList True r
  return $ f' : r'
  
-- expand top-level form one step, if possible
expandMacro1 :: Expr -> Comp (Maybe Expr)
expandMacro1 e@(EList (f : params)) = do
  res <- lift $ runErrorT $ evalExpr f
  e' <- case res of
          Right (fun@(Fun { funType = FunType { funCompilePhase = True }})) -> apply fun params
          _ -> return e
  if e' /= e then printTrace ("expandmacro-1: " ++ show e ++ " ==> " ++ show e') >> return (Just e') else return Nothing
expandMacro1 e = return Nothing

-- apply macroexpand-1 repeatedly at top level till it yields no new value
expandMacroTop :: Expr -> Comp Expr
expandMacroTop e = do
  exp <- expandMacro1 e
  if exp == Nothing then return () else printTrace $ "Expansion: " ++ show e ++ " ==> " ++ show exp
  maybe (return e) expandMacro exp

-- apply macroexpand both on top and then recursively inside the form
expandMacro :: Expr -> Comp Expr
expandMacro e = do
  topExp <- expandMacroTop e
  let children = seqElems topExp
  if exprType topExp /= "string" && isContainer topExp && (not . null) children then do
    expChildren <- mapM expandMacro children
    return $ makeSeq (seqType topExp) expChildren
  else
    return topExp

getSafeGlobal :: String -> Expr -> Comp Expr
getSafeGlobal name def = do
  val <- getGlobal name
  return $ maybe def id val

-- the post-expansion evaluation that can take place during the macro expansion stage
-- TODO: this is currently only 'def' and 'defmacro' expressions at top level
-- NOTE: this always returns the original expression, even if it was evaluated for
-- side effects
macroEvaluable = ["def", "defmacro", "defn"]
evalMacro :: Expr -> Comp Expr
evalMacro e@(EList (ESymbol sym : EString _ : _)) | elem sym macroEvaluable =
  printTrace ("Evaluating during expansion: " ++ show e) >> evalExpr e >> return e
evalMacro e = return e

prefixSymbols :: Comp [Expr]
prefixSymbols = getSafeGlobal "*prefix-symbols*" (EList []) >>= return . seqElems

isPrefixSymbol :: Expr -> Comp Bool
isPrefixSymbol e = prefixSymbols >>= return . elem e

infixSymbols :: Comp [Expr]
infixSymbols = getSafeGlobal "*infix-symbols*" (EList []) >>= return . seqElems

isInfixSymbol :: Expr -> Comp Bool
isInfixSymbol e = infixSymbols >>= return . elem e

backquote :: Int -> Expr -> Comp Expr
backquote depth e@(EList [ESymbol "`", expr]) = backquote (depth + 1) expr
backquote 0 e = evalExpr e
backquote depth e@(EList [ESymbol "~", expr]) = backquote (depth - 1) expr
backquote depth e | isSeq e = backquoteList depth (seqElems e) >>= return . makeSeq (seqType e)
                  | True = return $ wrapQuote (depth - 1) e

backquoteList :: Int -> [Expr] -> Comp [Expr]
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

-- Create an environment only having mappings for special forms and primitive functions

bootstrap :: Comp ()
bootstrap = do
  put . CompState $ S.emptyState
  setTracePat Nothing
  mapM_ (makePrimFun funFunType) primFuns
  mapM_ (makePrimFun specialFunType) primSpecials
  mapM_ setGlobal [("nil", ENil), ("false", EBool False), ("true", EBool True)]
  setGlobal ("*prefix-symbols*",
             (EList $ map ESymbol ["`", "'", "~", "~@"]))

bootstrapState :: IO CompState
bootstrapState = do
  (_, st) <- runComp bootstrap (CompState S.emptyState)
  return st

--
-- primitive functions
-- 

primFuns = [
  "rest", "apply", "print", "eval", "eval*", "slurp", "getline", "read*", "macroexpand-1", "macroexpand",
  "cons", "first", "type", "seq?", "seqable?", "container?", "seq", "conj",
  "get",
  "+", "-", "*", "div", "mod", "<", "=",
  "name", "str", "char",
  "trace", "fail", "exit",
  "unify", "get-global", "get-local", "set-global!", "set-local!",
  "stash!", "import-stash!", "reset-stash!", "get-globals", "get-locals",
  "reset-all!", "reset-local!" ]
primSpecials = ["do", "if", "dump", "quote", "fun", "backquote"]

makeNativeName :: String -> String
makeNativeName s = "_" ++ s

makePrimFun :: FunType -> String -> Comp ()
makePrimFun fType name = mapM_ (\n -> setGlobal (n, fun)) [natName, name] where
  fun = Fun { funLambda = Nothing, funName = Just name, funFun = Just $ prim name, funType = fType }
  natName = makeNativeName name

-- implementations of both functions and specials
prim :: String -> CompFun
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
prim "getline" _ = liftIO $ getLine >>= return . EString
prim "read*" ((EString s) : _) = readProgram s >>= return . EList
prim "macroexpand-1" (e : _) = expandMacro1 e >>= maybe (return e) return
prim "macroexpand" (e : _) = expandMacro e
prim "cons" (f : s : _) = return $ EList (f : seqElems s)
prim "first" (s : _) = return $ if null elems then ENil else head elems where
  elems = seqElems s
prim "type" (f : _) = return . EString . exprType $ f
prim "name" (n : _) | isNamed n = return . EString . exprName $ n
                    | True = throwError $ "Cannot get name of " ++ show n
prim "str" args = return . EString . Str.join "" . map exprStr $ args
prim "char" (e : _) = toChar e
prim "seq?" (s : _) = return . EBool $ isSeq s
prim "seqable?" (s : _) = return . EBool $ isSeqable s
prim "container?" (s : _) = return . EBool $ isContainer s
-- NOTE: seq on a map creates a FLAT list of keys and values interleaved!
prim "seq" (s : _) = let elems = seqElems s in
     return $ if null elems then ENil else EList elems
-- conj can add many elements, where maps expects sequences of key and value
-- for each added element
prim "conj" (s : adding) = foldM conj s adding
prim "nth" (s : (ENumber n) : _) = return $ if length elems > ind then elems !! ind else ENil where
  ind = fromInteger n
  elems = seqElems s
prim "get" ((EMap m) : key : _) = return $ maybe ENil id $ M.lookup key m
prim "+" s = numHandler (foldl (+) 0) s
prim "-" s = numHandler (\(n : ns) -> if ns==[] then - n else (foldl (-) n ns)) s
prim "*" s = numHandler (foldl (*) 1) s
prim "div" s = numHandler (foldl1 div) s
prim "mod" s = numHandler (foldl1 mod) s
prim "<" (p1 : p2 : []) = return $ EBool (p1 < p2)
prim "=" (p1 : p2 : []) = return $ EBool (p1 == p2)
prim "count" ((EMap m) : _) = return . ENumber . toInteger . M.size $ m
prim "count" (s : _) = return . ENumber . toInteger . length . seqElems $ s
prim "trace" (pat : _) = setTracePat (if isTruthy pat then Just . exprStr $ pat else Nothing) >>= return . maybe ENil EString
prim "fail" args = throwError $ Str.join " " $ map show args
prim "exit" _ = fail "programmatic exit"
prim "unify" (formal : actual : []) = unifyState formal actual >>= return . EBool
prim "stash!" [s, v] = stashLocal (exprName s, v) >> return ENil
prim "import-stash!" _ = importStash >>= return . EList . map (\(k, v) -> makeSeq  SeqVector [makeSymbol k, v])
prim "reset-stash!" _ = resetStash >> return ENil
prim "get-globals" _ = getGlobalBindings >>= return . EList . map (\(k, v) -> makeSeq SeqVector [ESymbol k, v])
prim "get-locals" _ = getLocalBindings >>= return . EList . map (\(k, v) -> makeSeq SeqVector [ESymbol k, v])
prim "reset-all!" _ = bootstrap >> return ENil
prim "reset-local!" _ = resetLocal >> return ENil

--
-- special forms, with parameters unevaluated
--
prim "set-global!" [ESymbol var, value] = do
  setGlobal (var, value)
  return value
prim "set-local!" [ESymbol var, value] = do
  setLocal (var, value)
  return value
prim "get-global" [ESymbol var] =
  getGlobal var >>= return . maybe ENil id
prim "get-local" [ESymbol var] =
  getLocal var >>= return . maybe ENil id
prim "do" params = if null params then return ENil else liftM last . mapM evalExpr $ params
prim "if" (condPart : thenPart : elsePart : []) = do
  cond <- evalExpr condPart
  evalExpr $ if isTruthy cond then thenPart else elsePart
prim "dump" _ = do 
  liftIO $ putStrLn "DUMP: "
  liftIO $ putStrLn "ENV = "
  dump
  return ENil
prim "quote" (param : _) = do
  return $ param
prim "fun" (funSpec : params) = do
  spec <- evalExpr funSpec
  makeLambda Nothing params $ createSpecFunType (seqElems spec)
prim "backquote" (s : _) = do
  backquote 1 s
prim fun args = throwError $ "Got a strange call of " ++ show fun ++ " on " ++ show args

makeLambda :: Maybe String -> [Expr] -> FunType -> Comp Expr
makeLambda name (s : body) fType = do
  let doBody = case body of
                [b] -> b
                _ -> (EList (ESymbol "do": body))
  outerLocal <- getLocalEnv
  return $ Fun { funName = name, funLambda = Just $ Lambda { lambdaParams = s, lambdaBody = doBody },
                 funType = fType, funFun = Just (\actuals -> do
    innerLocal <- getLocalEnv
    setLocalEnv outerLocal
    alright <- unifyState s $ EList actuals
    if alright then return ENil else (throwError $ "Could not bind formal parameters " ++ show s ++ " with actual parameters " ++ show (EList actuals) ++ " for function with body " ++ show body)
    val <- (if funReduce fType then substitute else evalExpr) doBody
    setLocalEnv innerLocal
    return val) }

numHandler :: ([Integer] -> Integer) -> CompFun
numHandler f params = do
  nums <- mapM num params
  return $ ENumber $ f nums

-- Substitute all variables, but keep all other expressions intact
substitute :: Expr -> Comp Expr
-- TODO: we use literals for the quoting prefixes; handle it properly!
substitute e@(EList (ESymbol name : _)) | elem name ["quote", "'"] = return e
substitute e | isContainer e =
  mapM substitute (seqElems e) >>=
  return . makeSeq (seqType e)
substitute e@(ESymbol name) =
  getVar name >>= return . maybe e id
substitute e = return e

defaultFunType = funFunType                           

createSpecFunType :: [Expr] -> FunType
createSpecFunType [] = defaultFunType
createSpecFunType ((EKeyword name Nothing) : rest) =
  let funType = createSpecFunType rest in
  case name of
    "call-by-name" -> funType { funByName = True }
    "expressive" -> funType { funExpressive = True }
    "reduce" -> funType { funReduce = True }
    "compile-time" -> funType { funCompilePhase = True }
    "runtime" -> funType { funRuntime = True }
    -- TODO: we just assume that any other keyword names the kind of function
    other -> funType { funTypeName = other }
createSpecFunType (_ : rest) = createSpecFunType rest

-- Some utilities

tryReadFile :: String -> IO String
tryReadFile = readFile
-- tryReadFile n = catch (readFile n)
--                     (\e -> throwError "Could not open file " ++ n ++ " due to: " ++ show (e :: IOException))
