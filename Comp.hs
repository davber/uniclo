{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Comp where

import Common
import Expr
import Env

data CompState = CompState { compLocalEnv :: Env, compGlobalEnv :: Env, compTraceFlag :: Bool }

type ComputationM = CompType CompState
type Computation = ComputationM Expr

instance Comp ComputationM where
  getTraceFlag = getState >>= return . traceFlag
  setTraceFlag flag = do
    env <- getState
    let oldFlag = traceFlag env
    let env' = env { traceFlag = flag }
    setState env'
    return oldFlag

