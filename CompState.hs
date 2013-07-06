{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}
module CompState where

import qualified Data.Map as Map

import Expr

type Binding= (String, Expr)
type BindingList = [Binding]

type Env = Map.Map String Expr
type EnvHandle = Int

data CompState = CompState { compLocalEnv :: Env, compGlobalEnv :: Env, compTraceFlag :: Bool }

getGlobalVar :: String -> CompState -> Maybe Expr
getGlobalVar name state = Map.lookup name $ compGlobalEnv state
getLocalVar :: String -> CompState -> Maybe Expr
getLocalVar name state = Map.lookup name $ compLocalEnv state

bindGlobalVar :: String -> Expr -> CompState -> CompState
bindGlobalVar name value state = state { compGlobalEnv = newEnv } where
  newEnv = Map.insert name value $ compGlobalEnv state
bindLocalVar :: String -> Expr -> CompState -> CompState
bindLocalVar name value state = state { compLocalEnv = newEnv } where
  newEnv = Map.insert name value $ compLocalEnv state

getLocalBindings :: CompState -> BindingList
getLocalBindings = Map.assocs . compLocalEnv

getGlobalBindings :: CompState -> BindingList
getGlobalBindings = Map.assocs . compGlobalEnv

getTrace :: CompState -> Bool
getTrace = compTraceFlag
setTrace :: Bool -> CompState -> CompState
setTrace flag s = s { compTraceFlag = flag }

emptyState :: CompState
emptyState = CompState { compLocalEnv = emptyEnv, compGlobalEnv = emptyEnv, compTraceFlag = False }
emptyEnv :: Env
emptyEnv = Map.empty
