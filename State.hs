{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}
module State where

import qualified Data.Map as Map

import Expr

type Binding m = (String, GExpr m)
type BindingList m = [Binding m]

type Env m = Map.Map String (GExpr m)
type EnvHandle = Int

data CompState m = CompState { compLocalEnv :: Env m, compGlobalEnv :: Env m, compTraceFlag :: Bool }

getGlobalVar :: CompState m => String -> Maybe (GExpr m)
getGlobalVar state name = Map.lookup name $ compLocalEnv state
getLocalVar :: CompState m => String -> Maybe (GExpr m)
getLocalVar state name = Map.lookup name $ compGlobalEnv state

bindGlobalVar :: CompState m -> String -> GExpr m -> CompState m
bindGlobalVar state name value = state { compGlobalEnv = newEnv } where
  newEnv = Map.insert name value $ compGlobalEnv state
bindLocalVar :: CompState m -> String -> GExpr m -> CompState m
bindLocalVar state name value = state { compLocalEnv = newEnv } where
  newEnv = Map.insert name value $ compLocalEnv state

getLocalBindings :: CompState m => BindingList m
getLocalBindings = Map.assocs . compLocalEnv

getGlobalBindings :: CompState m => BindingList m
getGlobalBindings = Map.assocs . compGlobalEnv

emptyState :: CompState m
emptyState = CompState { compLocalEnv = emptyEnv, compGlobalEnv = emptyEnv, compTraceFlag = False }
emptyEnv :: Env m
emptyEnv = Map.empty
