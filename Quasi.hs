{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, DataKinds #-}
module Quasi where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Data.Typeable
import Data.Data

import Expr

deriving instance Typeable Expr
