{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
module Quasi where
import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

import Parse
import Expr
import Comp

uniclo :: QuasiQuoter
uniclo = QuasiQuoter { quoteExp = quoteExpr }

quoteExpr str = do loc <- TH.location
                   let pos =  (TH.loc_filename loc,
                                 fst (TH.loc_start loc),
                                 snd (TH.loc_start loc))
                   let exprs = parseProgramText str
                   dataToExpQ (const Nothing) (2::Int)

