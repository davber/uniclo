{-# LANGUAGE FlexibleContexts, UndecidableInstances, Rank2Types #-}
module Parse where

import Prelude hiding (catch, lex)
import Control.Monad (liftM)
import Control.Applicative hiding (many, optional)
import Text.ParserCombinators.Parsec hiding (State, (<|>))
import Text.ParserCombinators.Parsec.Token as P
import Text.Parsec.Numbers as Num
import Text.ParserCombinators.Parsec.Char
import Text.Parsec.Language (haskellDef)

import Common
import Expr

-- utility to compose an unary function with a binary one
(.*) = (.) . (.)

--
-- The parser, using Parsec
--

-- The reader consists of parsing and then expanding the forms

-- The tokenizer

language = P.LanguageDef {
    commentStart = "",
    commentEnd = "",
    commentLine = ";",
    nestedComments = False,
    identStart = oneOf "!#$%&|*+-/<=>?_." <|> letter,
    identLetter = oneOf "!#$%&|*+-<=>?_.'" <|> alphaNum,
    opStart = oneOf "~#`'",
    opLetter = oneOf "@",
    reservedNames = [],
    reservedOpNames = [],
    caseSensitive = True
  }
lexer' = P.makeTokenParser language 
lexer = lexer' { whiteSpace = skipMany1 (char ',') <|> P.whiteSpace lexer' }
lex = P.lexeme lexer
ws = P.whiteSpace lexer
sym = P.symbol lexer
ident = P.identifier lexer
oper = P.operator lexer
parseProgram = ws *> many parseGExpr <* eof
parsePadGExpr = lex parseGExpr
parseChar = EChar . getCharLiteral <$> (char '\\' *> (try ident <|> (anyChar >>= return . (:[]))))
parseString = EString <$> P.stringLiteral lexer <?> "string"
parseNumber =  ENumber <$> (try . lex) Num.parseIntegral <?> "number"
parseKeyword = flipNs .* EKeyword <$>
               lex (char ':' *>
                P.identifier lexer) <*>
               optionMaybe (char '/' *> ident)
               <?> "keyword"
parseSymbol = ESymbol <$> lex (ident <|> oper)
              <?> "symbol"
parseAtom =  choice [parseNumber, parseChar, parseString, parseKeyword, parseSymbol]
             <?> "atom"
parseSeq seqType = makeSeqFlat seqType <$> 
                   (sym (leftDelim seqType) *> many parseGExpr <* sym (rightDelim seqType))
                   <?> "list"
parseList = parseSeq SeqList
parseVector = parseSeq SeqVector
parseSet = parseSeq SeqSet
parseMap = parseSeq SeqMap
parseGExpr = parseList <|> parseVector <|> parseSet <|> parseMap <|> parseAtom

type ParseResult = forall m. Either Err [GExpr m]

parseProgramText :: String -> ParseResult
parseProgramText input = either (Left . show) Right $ parse parseProgram "clojure" input
parseGExprText :: String -> ParseResult
parseGExprText input = either (Left . show) (Right . (\x -> [x])) $ parse parseGExpr "clojure" input
