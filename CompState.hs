{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}
module CompState where

import qualified Data.Map as Map

import Expr

type Binding m = (String, GExpr m)
type BindingList m = [Binding m]

type Env m = Map.Map String (GExpr m)

data CompPhase = PhaseRead | PhaseExpand | PhaseInterpret | PhaseCompile { compileTarget :: String, compileOutput :: String }

data CompState m = CompState { compLocalEnv :: Env m, compGlobalEnv :: Env m, compTraceFlag :: Bool, compPhase :: CompPhase, compLocalStash :: BindingList m }

getGlobalVar :: String -> CompState m -> Maybe (GExpr m)
getGlobalVar name state = Map.lookup name $ compGlobalEnv state
getLocalVar :: String -> CompState m -> Maybe (GExpr m)
getLocalVar name state = Map.lookup name $ compLocalEnv state

bindGlobalVar :: String -> GExpr m -> CompState m -> CompState m
bindGlobalVar name value state = state { compGlobalEnv = newEnv } where
  newEnv = Map.insert name value $ compGlobalEnv state
bindLocalVar :: String -> GExpr m -> CompState m -> CompState m
bindLocalVar name value state = state { compLocalEnv = newEnv } where
  newEnv = Map.insert name value $ compLocalEnv state

getLocalBindings :: CompState m -> BindingList m
getLocalBindings = Map.assocs . compLocalEnv

getGlobalBindings :: CompState m -> BindingList m
getGlobalBindings = Map.assocs . compGlobalEnv

getTrace :: CompState m -> Bool
getTrace = compTraceFlag
setTrace :: Bool -> CompState m -> CompState m
setTrace flag s = s { compTraceFlag = flag }

getCompPhase :: CompState m -> CompPhase
getCompPhase s = compPhase s
setCompPhase :: CompPhase -> CompState m -> CompState m
setCompPhase phase s = s { compPhase = phase }

emptyState :: CompState m
emptyState = CompState { compLocalEnv = emptyEnv, compGlobalEnv = emptyEnv, compTraceFlag = False, compPhase = PhaseInterpret, compLocalStash = [] }
emptyEnv :: Env m
emptyEnv = Map.empty
