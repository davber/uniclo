module Value where

import Expr

type GCompFun m = [Value m] -> m (Value m)
data FunType = FunFun | FunMacro | FunSpecial
data Value m = Literal Expr | Fun FunType Expr GCompFun m
