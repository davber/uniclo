{-# LANGUAGE Rank2Types, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, GADTs, ImpredicativeTypes, FlexibleContexts, ScopedTypeVariables #-}
module Common where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.State.Class

type Err = String

-- Computations can either (i) yield a value or (ii) yield an error
-- AND can also interact with the environment
-- We encapsulate this by a three-layer monadic pie:
-- Error - State - IO

class (Show e, Eq e, Ord e) => ExprM e
data Binding a where
  Binding :: ExprM a => String -> a -> Binding a
instance Show a => Show (Binding a) where
  show (Binding name val) = show (name, val)
type BindingList a = [Binding a]

class (MonadError Err m, MonadIO m) => Comp m where
  --
  -- chaging environment structures
  --
  -- getting and setting local and global environments is purposely
  -- opaque
  -- setting env also returns the current one
  getLocalEnv :: forall env. m env
  setLocalEnv :: forall env. env -> m env
  getGlobalEnv :: forall env. m env
  setGlobalEnv :: forall env. env -> m env
  -- create a new empty local scope
  pushScope :: m ()
  -- pop the top (or bottom...) local scope
  popScope :: m ()

  --
  -- access to variables
  --
  getLocal :: ExprM a => String -> m (Maybe a)
  setLocal :: ExprM a => Binding a -> m ()
  getGlobal :: ExprM a => String -> m (Maybe a)
  setGlobal :: ExprM a => Binding a -> m ()
  getLocalBindings :: m (ExprM a => BindingList a)
  getGlobalBindings :: m (ExprM a => BindingList a)
  addLocalBindings :: ExprM a => BindingList a -> m ()
  addGlobalBindings :: ExprM a => BindingList a -> m ()

  setTraceFlag :: Bool -> m Bool
  getTraceFlag :: m Bool
  printTrace :: String -> m ()
  printTrace text = do
    flag <- getTraceFlag
    if flag then liftIO $ putStrLn $ "TRACE: " ++ text else return ()
  runComp :: forall b s. m b -> s -> m (Either Err b, s)
  compShow :: m String
  compShow = do
    locals <- getLocalBindings
    globals <- getGlobalBindings
    trace <- getTraceFlag
    return $ "Tracing: " ++ show trace ++ "\nLocal: " ++
             show locals ++ "\nGlobal: " ++ show globals
  dump :: m ()
  dump = compShow >>= liftIO . print
  getState :: forall s. m s
  setState :: forall s. s -> m ()

type CompType s = ErrorT Err (StateT s IO)
