module Main where

import Data.Either
import Data.List.Utils
import Data.List(sort, group)
import Text.Show.Functions
import Text.ParserCombinators.Parsec hiding (State, (<|>))
import Text.ParserCombinators.Parsec.Char

import Common
import Expr
import Eval
import Parse
import qualified CompState as S
import Comp

main :: IO ()
main = repl . CompState $ S.emptyState

repl :: CompState -> IO ()
repl env = do
  -- we emulate a loading of the prelude at the beginning of REPL
  (value, st) <- runComp (evalStr "(eval* (read* (slurp \"prelude.lsp\")))")
    $ CompState . S.setTrace True . runCompState $ env
  either fail (\_ -> replCont (CompState . S.setTrace False . runCompState $ st) "") value

replCont :: CompState -> String -> IO ()
replCont env parsed = do
  putStr $ if length parsed > 0 then ">> " else "> "
  -- three cases: (i) regular line, (ii) continuation line (ending with \) or (iii) REPL command
  line <- getLine
  let text = parsed ++ "\n" ++ line
  if endswith "\\" text then replCont env (init text) else replEval env text

replEval :: CompState -> String -> IO ()
replEval env parsed = do
  (vals, st) <- runComp (evalStr parsed) env
  either (\x -> putStr "ERROR: " >> putStrLn x) (mapM_ print) vals
  replCont (either (\_ -> st) (\vs -> (if length vs > 0 then CompState . S.bindGlobalVar "$" (last vs) . runCompState else id) st) vals) ""


-- Utilities to simplify parsing and evaluating individual expressions

preludeEnv :: IO CompState
preludeEnv = do
--  (_, st) <- runStateT (runErrorT $ evalStr "(eval* (read* (slurp \"prelude.lsp\")))") createEmptyEnv
--  return st
  let env = S.bindGlobalVar "*prefix-symbols*" (EList $ map ESymbol ["`", "'", "~", "~@"]) S.emptyState
  return . CompState $ S.setTrace True env

testParseList :: String -> [Expr]
testParseList = either ((:[]) . EString . show) id . parse parseProgram ""

testParse :: String -> Expr
testParse = either (EString .show) id . parse parseExpr ""

testExpand1 :: Expr -> IO Expr
testExpand1 e = do
  env <- preludeEnv
  (val, _) <- runComp (expandMacro1 e) env
  return $ either (EString . show) (maybe ENil id) val

testExpand :: Expr -> IO Expr
testExpand e = do
  env <- preludeEnv
  (val, _) <- runComp (expandMacro e) env
  return $ either EString id val

testShuffle :: [Expr] -> IO [Expr]
testShuffle e = do
  env <- preludeEnv
  (val, _) <- runComp (shufflePrefixList e) env
  return $ either ((:[]) . EString) id val

testEval :: Expr -> IO Expr
testEval e = do
   env <- preludeEnv
   (val, _) <- runComp (evalExpr e) env
   return $ either EString id val
