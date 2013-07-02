{-# LANGUAGE ExistentialQuantification, GADTs, LiberalTypeSynonyms, RankNTypes, ScopedTypeVariables, FlexibleContexts, ImpredicativeTypes #-}
module Eval where

import Control.Monad.Error
import Control.Monad.State
import Control.Exception
import qualified Data.String.Utils as Str
import qualified Data.Map as M

import Common
import Expr
import Parse

type ExprBindingList = BindingList Expr

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
unifyState :: forall m. Comp m => Expr -> Expr -> m Bool
unifyState e1 e2 = do
  let (bindings, flag) = maybe ([], False) (\bindings -> (bindings, True)) $ unifyBindings e1 e2
  printTrace $ "Unification: " ++ show e1 ++ " <|> " ++ show e2 ++ " ==> " ++
               if flag then show bindings else "failed!" 
  addLocalBindings bindings
  return flag

-- Unify two terms, having the latest bindings at the front of the list
unifyBindings :: Expr -> Expr -> Maybe ExprBindingList
unifyBindings e1 e2 = unify e1 e2 []

-- Unify two tems, with bindings to the left, adding to the existing
-- binding list
unify :: Expr -> Expr -> ExprBindingList -> Maybe ExprBindingList
unify (ESymbol name) value b = Just $ (Binding name value) : b
unify s1 s2 b | isSeqable s1 && isSeqable s2 = unifyList (seqElems s1) (seqElems s2) b
unify s1 s2 b | s1 == s2 = Just b
              | True = Nothing

unifyList :: [Expr] -> [Expr] -> ExprBindingList -> Maybe ExprBindingList
unifyList [] [] = return
unifyList (ESymbol "&" : rest : _) other = unify rest (EList other)
unifyList (f1:r1) (f2:r2) = (\b -> unify f1 f2 b >>= unifyList r1 r2)
unifyList _ _ = (\_ -> Nothing)

-- applies macro expansion to a program
expandProgram :: Comp m => [Expr] -> m [Expr]
expandProgram exprs = printTrace "*** Expanding program ***" >> mapM (\e -> expandMacro e >>= evalMacro) exprs
-- reading a program both parses and read-expands it
readProgram :: Comp m => String -> m [Expr]
readProgram text = do
  printTrace "*** Parsing program ***"
  either fail (\expr -> printTrace "*** Reading program ***" >> shufflePrefixList expr) $ parseProgramText text

--
-- Evaluator, yielding (and executing...) a computation
--

evalProgram :: Comp m => [Expr] -> m [Expr]
evalProgram exprs = printTrace "*** Evaluating program ***" >> mapM evalExpr exprs

evalExpr :: Comp m => Expr -> m Expr
evalExpr e@(EKeyword _ _) = return e
evalExpr e@(EChar _) = return e
evalExpr (ESymbol sym) = do
  val <- getLocal sym
  return $ maybe ENil id val
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
evalExpr expr = fail $ "Could not evaluate " ++ show expr

-- evalStr evalues expression by expression, thus allowing for definitions
-- of reader macros
evalStr :: Comp m => String -> m [Expr]
evalStr s = readProgram s >>= expandProgram >>= evalProgram

num :: Comp m => Expr -> m Integer
num (ENumber numb) = return numb
num e = fail $ show e ++ " is not a number"

apply :: Comp m => Expr -> [Expr] -> m Expr
apply (Fun (Lambda _ _ _ f)) params = mapM evalExpr params >>= f
apply (Macro (Lambda _ _ _ f)) params = f params >>= evalExpr
apply (ESpecial _ f) params = f params
apply other args = fail $ "Not a proper function application: " ++ show (EList (other : args))

--
-- Reader prefix reshuffling, which makes prefix symbols regular prefix forms
-- NOTE: we only care about definitions of the *prefix-symbols* forms for controlling
-- these prefix symbols!
--

shufflePrefix :: Comp m => Expr -> m Expr
shufflePrefix defE@(EList [ESymbol "def", ESymbol "*prefix-symbols*", expr]) = do
  val <- evalExpr expr -- NOTE: usually a literal sequence
  setGlobal $ Binding "*prefix-symbols*" val
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

shufflePrefixList :: Comp m => [Expr] -> m [Expr]
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
expandMacro1 :: Comp m => Expr ->  m (Maybe Expr)
expandMacro1 e@(EList ((Macro (Lambda n _ _ f)) : params)) = do
  val <- f params
  printTrace $ "Inside macroexpand-1: " ++ show e ++ " ==> " ++ show val
  return . Just $ val
expandMacro1 e@(EList (f : params)) = do
  s <- getState
  (fval, _) <- runComp (expandMacro f >>= evalExpr) s
  either (\err -> printTrace ("warning when trying to expand form " ++ show e ++ ": " ++ show err) >> return Nothing) (\val -> if isMacro val then expandMacro1 (EList (val : params)) else return Nothing) fval
expandMacro1 e = return Nothing


-- apply macroexpand-1 repeatedly at top level till it yields no new value
expandMacroTop :: Comp m => Expr -> m Expr
expandMacroTop e = do
  exp <- expandMacro1 e
  if exp == Nothing then return () else printTrace $ "Expansion: " ++ show e ++ " ==> " ++ show exp
  maybe (return e) expandMacro exp

-- apply macroexpand both on top and then recursively inside the form
expandMacro :: Comp m => Expr -> m Expr
expandMacro e = do
  topExp <- expandMacroTop e
  let children = seqElems topExp
  if exprType topExp /= "string" && isContainer topExp && (not . null) children then do
    expChildren <- mapM expandMacro children
    return $ makeSeq (seqType topExp) expChildren
  else
    return topExp

getSafeGlobal :: Comp m => String -> Expr -> m Expr
getSafeGlobal name def = do
  val <- getGlobal name
  return $ maybe def id val

-- the post-expansion evaluation that can take place during the macro expansion stage
-- TODO: this is currently only 'def' and 'defmacro' expressions at top level
-- NOTE: this always returns the original expression, even if it was evaluated for
-- side effects
macroEvaluable = ["def", "defmacro", "defn"]
evalMacro :: Comp m => Expr -> m Expr
evalMacro e@(EList (ESymbol sym : EString _ : _)) | elem sym macroEvaluable =
  printTrace ("Evaluating during expansion: " ++ show e) >> evalExpr e >> return e
evalMacro e = return e

prefixSymbols :: Comp m => m [Expr]
prefixSymbols = getSafeGlobal  "*prefix-symbols*" (EList []) >>= return . seqElems

isPrefixSymbol :: Comp m => Expr -> m Bool
isPrefixSymbol e = prefixSymbols >>= return . elem e

backquote :: Comp m => Int -> Expr -> m Expr
backquote depth e@(EList [ESymbol "`", expr]) = backquote (depth + 1) expr
backquote 0 e = evalExpr e
backquote depth e@(EList [ESymbol "~", expr]) = backquote (depth - 1) expr
backquote depth e | isSeq e = backquoteList depth (seqElems e) >>= return . makeSeq (seqType e)
                  | True = return $ wrapQuote (depth - 1) e

backquoteList :: Comp m => Int -> [Expr] -> m [Expr]
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

bootstrapState :: Comp m => m ()
bootstrapState = do
  setTraceFlag False
  mapM_ makePrimLambda primFuns
  mapM_ makePrimSpecial primSpecials
  mapM_ setGlobal [Binding "nil" ENil, Binding "false" $ EBool False,
                   Binding "true" $ EBool True]

--
-- primitive functions
-- 

primFuns = [
  "rest", "apply", "print", "eval", "eval*", "slurp", "read*", "macroexpand-1", "macroexpand",
  "cons", "first", "type", "seq?", "seqable?", "container?", "seq", "conj",
  "+", "-", "*", "div", "mod", "<", "=", "list", "count",
  "name", "str",
  "trace", "fail"]
primSpecials = ["def", "do", "if", "dump", "quote", "unify", "lambda", "macro", "backquote"]

makePrimLambda :: Comp m => String -> m ()
makePrimLambda name = setGlobal $ Binding name $ Fun $ Lambda name ENil ENil $ prim name
makePrimSpecial :: Comp m => String -> m ()
makePrimSpecial name = setGlobal $ Binding name $ ESpecial name $ prim name

-- implementations of both functions and specials
prim :: Comp m => String -> CompFun m
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
prim "name" (n : _) | isNamed n = return . EString . exprName $ n
                    | True = fail $ "Cannot get name of " ++ show n
prim "str" args = return . EString . Str.join "" . map exprStr $ args
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
prim "trace" (flag : _) = setTraceFlag (isTruthy flag) >>= return . EBool
prim "fail" args = fail $ Str.join " " $ map show args

--
-- special forms, with parameters unevaluated
--
-- TODO: allow def with zero or more than 1 value arguments
prim "def" [ESymbol var, value] = do
     evalExpr <- evalExpr value
     setGlobal $ Binding var evalExpr
     return evalExpr
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
prim "unify" (formal : actual : []) = unifyState formal actual >>= return . EBool
prim "lambda" (s : body) = do
      let doBody = case body of
                     [b] -> b
                     _ -> (EList (ESymbol "do": body))
      outerLocal <- getLocalEnv
      return $ Fun $ Lambda "lambda" s doBody $ (\actuals -> do
        innerLocal <- setLocalEnv outerLocal
        alright <- unifyState s $ EList actuals
        if alright then return ENil else (fail $ "Could not bind formal parameters " ++ show s ++ " with actual parameters " ++ show (EList actuals) ++ " for function with body " ++ show body)
        val <- evalExpr doBody
        setLocalEnv innerLocal
        return val)
-- TODO: the macro definition is identical to that of "lambda"!
prim "macro" (s : body) = do
      let doBody = case body of
                     [b] -> b
                     _ -> (EList (ESymbol "do": body))
      outerLocal <- getLocalEnv
      return $ Macro $ Lambda "macro" s doBody $ (\actuals -> do
        innerLocal <- setLocalEnv outerLocal                
        alright <- unifyState s $ EList actuals
        if alright then return ENil else (fail $ "Could not bind formal parameters " ++ show s ++ " with actual parameters " ++ show (EList actuals) ++ " for function with body " ++ show body)
        expanded <- evalExpr doBody
        setLocalEnv innerLocal
        return expanded)
prim "backquote" (s : _) = do
  backquote 1 s

prim fun args = fail $ "Got a strange call of " ++ show fun ++ " on " ++ show args

numHandler :: ([Integer] -> Integer) -> CompFun m
numHandler f params = do
  nums <- mapM num params
  return $ ENumber $ f nums

-- Some utilities

tryReadFile :: String -> IO String
tryReadFile = readFile
-- tryReadFile n = catch (readFile n)
--                     (\e -> fail "Could not open file " ++ n ++ " due to: " ++ show (e :: IOException))
