{-# LANGUAGE ExistentialQuantification, GADTs, LiberalTypeSynonyms, RankNTypes, ImpredicativeTypes, PolyKinds, FlexibleContexts #-}
module Env where

import qualified Data.Map as Map
import Data.Maybe
import Common
import Expr

-- Expressions evaluate to Herbrand values

type Bindings = Map.Map String Expr
data Env = Env { globalEnv :: Bindings,
                 localEnv :: Bindings,
                 traceFlag :: Bool }

getVar :: Env -> String -> Maybe Expr
getVar e var = listToMaybe $ catMaybes [(Map.lookup var $ localEnv e),
                                        (Map.lookup var $ globalEnv e)]

envBindVar :: Env -> String -> Expr -> Env
envBindVar e k v = e { globalEnv = Map.insert k v $ globalEnv e }

resetLocal :: Env -> Env
resetLocal env = env { localEnv = createEmptyBindings }

createEmptyBindings :: Bindings
createEmptyBindings = Map.empty

combineEnv :: Env -> Bindings -> Env
combineEnv e bindings = e { localEnv = Map.union bindings $ localEnv e }
