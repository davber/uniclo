module Expr where

import Control.Monad.Error
import Control.Monad.State
import qualified Data.String.Utils as Str
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Char
import Data.Typeable

data Lambda = Lambda { lambdaName :: String,
                       lambdaParams :: Expr,
                         lambdaBody :: Expr }

instance Show Lambda where
  show (Lambda name params expr _) = name ++
    if isTruthy params then ": " ++ show params ++ " --> " ++ show expr ++ ")" else ""

data Expr =
  EKeyword String (Maybe String) |
  ESymbol String |
  ENumber Integer |
  EString String |
  EChar Char |
  EBool Bool |
  ENil |
  ELambda Lambda |
  ESpecial String |
  EList [Expr] |
  EVector [GExpr m] |
  ESet (S.Set (GExpr m)) |
  EMap (M.Map (GExpr m) (GExpr m))

instance Show (GExpr m) where
  show (EKeyword s Nothing) = ":" ++ s
  show (EKeyword s (Just ns)) = ":" ++ ns ++ "/" ++ s
  show (ESymbol s) = s
  show (EString s) = "\"" ++ s ++ "\""
  show (EChar c) = "\\" ++ showLitChar c ""
  show (ENumber num) = show num
  show (EBool b) = if b then "true" else "false"
  show ENil = "nil"
  show (Fun lambda@(Lambda {})) = "[fun]" ++ show lambda
  show (Macro lambda@(Lambda {})) = show lambda
  show (ESpecial s _) = "[special]" ++ s
  show (EMap m) = "{" ++ Str.join ", " (map (\(k,v) -> show k ++ " " ++ show v) $ M.assocs m) ++ "}"
  show e | isContainer e = leftDelim (seqType e) ++ (Str.join " " $ map show elems) ++ rightDelim (seqType e) where
    elems = seqElems e

instance Eq (GExpr m) where
  EKeyword ns1 s1 == EKeyword ns2 s2 = ns1 == ns2 && s1 == s2
  ESymbol s1 == ESymbol s2 = s1 == s2 
  EChar c1 == EChar c2 = c1 == c2
  ENumber num1 == ENumber num2 = num1 == num2
  EString s1 == EString s2 = s1 == s2
  EBool b1 == EBool b2 = b1 == b2
  ENil == ENil = True
  Fun (Lambda n1 p1 e1 _) == Fun (Lambda n2 p2 e2 _) = n1 == n2 && e1 == e2 && p1 == p2
  ESpecial s1 _ == ESpecial s2 _ = s1 == s2
  seq1 == seq2 | isContainer seq1 && isContainer seq2 =
    seqType seq1 == seqType seq2 && seqElems seq1 == seqElems seq2
  _ == _ = False
lexico comps = if length diffs == 0 then EQ else head diffs where diffs = filter (/= EQ) comps

instance Ord (GExpr m) where
  EKeyword ns1 s1 `compare` EKeyword ns2 s2 = lexico [ns1 `compare` ns2, s1 `compare` s2]
  ESymbol s1 `compare` ESymbol s2 = s1 `compare` s2
  ENumber s1 `compare` ENumber s2 = s1 `compare` s2
  EString s1 `compare` EString s2 = s1 `compare` s2
  seq1 `compare` seq2 | isContainer seq1 && isContainer seq2 =
    (seqType seq1, seqElems seq1) `compare` (seqType seq2, seqElems seq2)
  e1 `compare` e2 = show e1 `compare` show e2

-- S-Exprs and more semantic representations; i.e., we combine syntax
-- and (denotational) semantics, in a Herbrand manner
--

data SeqType = SeqList | SeqVector | SeqMap | SeqSet | SeqString  deriving (Show, Read, Eq, Ord)
leftDelim SeqList = "("
leftDelim SeqVector = "["
leftDelim SeqSet = "#{"
leftDelim SeqMap = "{"
rightDelim SeqList = ")"
rightDelim SeqVector = "]"
rightDelim SeqSet = "}"
rightDelim SeqMap = "}"

-- is the expression a proper sequence already?
-- NOTE: expressions can be seqable, turned into a sequence by seqElems
isSeq :: GExpr m -> Bool
isSeq (EList _) = True
isSeq (EVector _) = True
isSeq (ESet _) = True
isSeq (EMap _) = False
isSeq (EString _) = False
isSeq _ = False

-- is the expression comvertible into a sequence, i.e., seqable?
isSeqable :: GExpr m -> Bool
isSeqable e | isSeq e = True
isSeqable (EString _) = True
isSeqable (EMap _) = True
isSeqable _ = False

-- can expression contain sub expressions?
isContainer :: GExpr m -> Bool
isContainer e | isSeq e = True
isContainer (EMap _) = True
isContainer _ = False

seqType :: GExpr m -> SeqType
seqType (EList _) = SeqList
seqType (EVector _) = SeqVector
seqType (ESet _) = SeqSet
seqType (EMap _) = SeqMap

seqElems :: GExpr m -> [GExpr m]
seqElems (EList es) = es
-- NOTE: the elements are stored in reverse inside the vector construct
seqElems (EVector es) = reverse es
seqElems (ESet s) = S.elems s
seqElems (EMap m) = map (\(k,v) -> makeSeq SeqVector [k, v]) $  M.assocs m
seqElems (EString s) = map (\c -> EChar c) s
seqElems x = []

isEmpty :: GExpr m -> Bool
isEmpty s = case seqElems s of
  (_:_) -> True
  _ -> False

seqFirst :: GExpr m -> GExpr m
seqFirst e = let elems = seqElems e in
  if null elems then ENil else head elems

seqRest :: GExpr m -> [GExpr m]
seqRest e = let elems = seqElems e in
  if null elems then [] else tail elems

-- make a seqable object from a natural sequence of elements for that type
makeSeq :: SeqType -> [GExpr m] -> GExpr m
makeSeq SeqList = EList
makeSeq SeqSet = ESet . S.fromList
makeSeq SeqVector = EVector . reverse
-- NOTE: the sequence provided to a map consists of binary sequences, holding key and value
makeSeq SeqMap = EMap . M.fromList . map (\elem -> let (k:v:[]) = seqElems elem in (k,v))

-- create pairs of consecutive elements, in the form of EVectors
pairs :: [GExpr m] -> [GExpr m]
pairs [] = []
pairs (a:b:r) = makeSeq SeqVector [a, b] : pairs r
pairs [a] = [makeSeq SeqVector [a, ENil]] -- TODO: ad hoc for a strange case...

-- make a seqable object from a flat list of elements
makeSeqFlat :: SeqType -> [GExpr m] -> GExpr m
makeSeqFlat SeqMap = makeSeq SeqMap . pairs
makeSeqFlat seqType = makeSeq seqType

isTruthy :: GExpr m -> Bool
isTruthy ENil = False
isTruthy (EBool False) = False
isTruthy _ = True

exprType :: GExpr m -> String
exprType (Fun {}) = "fun"
exprType (EKeyword {}) = "keyword"
exprType (ENumber {}) = "number"
exprType (ESymbol {}) = "symbol"
exprType (EChar {}) = "char"
exprType (EString {}) = "string"
exprType (ENil {}) = "nil"
exprType (ESpecial {}) = "special"
exprType (EMap {}) = "map"
exprType (EList {}) = "list"
exprType (EVector {}) = "vector"
exprType (ESet {}) = "set"
exprType e | isSeqable e = "seq"
exprType e = "none"

printShow :: GExpr m -> String
printShow (EString s) = s
printShow x = show x

flipNs (EKeyword ns (Just s)) = EKeyword s (Just ns)
flipNs x = x

isSpecial :: GExpr m -> Bool
isSpecial (ESpecial _ _) = True
isSpecial _ = False

isMacro :: GExpr m -> Bool
isMacro (Macro _) = True
isMacro _ = False

-- string and char utils

getCharLiteral :: String -> Char
getCharLiteral [c] = c
-- TODO: implement properly
getCharLiteral x = '?'

isNamed :: GExpr m -> Bool
isNamed (EKeyword {}) = True
isNamed (ESymbol {}) = True
isNamed (EString {}) = True
isNamed _ = False

exprName :: GExpr m -> String
exprName (EKeyword name _) = name
exprName (ESymbol name) = name
exprName (EString s) = s

exprStr :: GExpr m -> String
exprStr (EString s) = s
exprStr (EChar c) = [c]
exprStr e = show e

-- backquote tracks the nesting level of backquotes, where 1
-- indicates that we are at the top level of a backquoted form,
-- and 0 that we are one unquote down from that, i.e., ready to evaluate

wrapQuote :: Int -> GExpr m -> GExpr m
wrapQuote 0 e = e
wrapQuote depth e = EList [(ESymbol "quote"), (wrapQuote (depth - 1) e)]

name :: GExpr m -> Maybe String
name (ESymbol s) = Just s
name _ = Nothing

conj :: GExpr m -> GExpr m -> GExpr m
conj (EList s) e = EList (e:s)
-- NOTE: the vector is stored in reverse inside the construct
conj (EVector s) e = EVector (e : s)
-- NOTE: conj:ing to a map requires a seqable element with at least two
-- elements, being the new key and value to be added
conj (EMap m) e = let (k:v:_) = seqElems e in EMap $ M.insert k v m
conj (ESet s) e = ESet $ S.insert e s
