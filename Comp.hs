{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, InstanceSigs, MultiParamTypeClasses, FlexibleContexts #-}
module Comp where
import qualified Data.Map as M
import Data.List((!!))
import Control.Monad.State
import Control.Monad.Error

import Common
import Expr
import qualified CompState as S

newtype CompState = CompState { runCompState :: S.CompState }
type Env = S.Env

type CompType s = ErrorT Err (StateT s IO)
type Comp = CompType CompState

type Binding = S.Binding
type BindingList = S.BindingList

-- Computations can either (i) yield a value or (ii) yield an error
-- AND can also interact with the environment
-- We encapsulate this by a three-layer monadic pie:
-- Error - State - IO

-- TODO: look over this strategy of threading the computation monad through
-- the supposedly syntactical expression constructs; the problem with existential
-- types is that there is much we can do with the returned values, though

--
-- chaging environment structures
--

getLocalEnv :: Comp Env
getLocalEnv = get >>= return . S.compLocalEnv . runCompState
-- setting an environment yields the old one
setLocalEnv :: Env -> Comp Env
setLocalEnv env = do
  s <- get
  let oldEnv = S.compLocalEnv . runCompState $ s
  let s' = (runCompState s) { S.compLocalEnv = env }
  put . CompState $ s'
  return oldEnv

--
-- access to variables
--
getLocal :: String -> Comp (Maybe Expr)
getLocal name = get >>= return . S.getLocalVar name . runCompState
setLocal :: Binding -> Comp ()
setLocal (name, value) = do
  s <- get
  let s' = S.bindLocalVar name value . runCompState $ s
  put . CompState $ s'
getGlobal :: String -> Comp (Maybe Expr)
getGlobal name = get >>= return . S.getGlobalVar name . runCompState
setGlobal :: Binding -> Comp ()
setGlobal (name, value) = do
  s <- get
  let s' = S.bindGlobalVar name value . runCompState $ s
  put . CompState $ s'
getVar :: String -> Comp (Maybe Expr)
getVar name = getLocal name >>=
  maybe (getGlobal name) (return . Just)
getLocalBindings :: Comp BindingList
getLocalBindings = get >>= return . M.assocs . S.compLocalEnv . runCompState
getGlobalBindings :: Comp BindingList
getGlobalBindings = get >>= return . M.assocs . S.compGlobalEnv . runCompState
addLocalBindings :: BindingList -> Comp ()
addLocalBindings bindings = do
  s <- get
  let newLocals = foldl (\m (k, v) -> M.insert k v m)  (S.compLocalEnv . runCompState $ s) bindings
  put . CompState $ (runCompState s) { S.compLocalEnv = newLocals }
addGlobalBindings :: BindingList -> Comp ()
addGlobalBindings bindings = do
  s <- get
  let newGlobals = foldl (\m (k, v) -> M.insert k v m) (S.compGlobalEnv . runCompState $ s) bindings
  put . CompState $ (runCompState s) { S.compGlobalEnv = newGlobals }
setTraceFlag :: Bool -> Comp Bool
setTraceFlag flag = do
  s <- get
  let oldFlag = S.compTraceFlag . runCompState $ s
  let s' = (runCompState s) { S.compTraceFlag = flag }
  put . CompState $ s'
  return oldFlag
getTraceFlag :: Comp Bool
getTraceFlag = get >>= return . S.compTraceFlag . runCompState
printTrace :: String -> Comp ()
printTrace text = do
  flag <- getTraceFlag
  if flag then liftIO $ putStrLn $ "TRACE: " ++ text else return ()
compShow :: Comp String
dump :: Comp ()
dump = compShow >>= liftIO . print
compShow = do
  -- NOTE: need to deconstruct the type to get to the ExprM context
  locals <- getLocalBindings
  globals <- getGlobalBindings
  trace <- getTraceFlag
  return $ "Tracing: " ++ show trace ++ "\nLocal: " ++
           show locals ++ "\nGlobal: " ++ show globals

type CompFun = [Expr] -> Comp Expr

runComp :: Comp a -> CompState -> IO (Either Err a, CompState)
runComp m = runStateT (runErrorT m)

