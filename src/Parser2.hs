{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module Parser2 (stringToExpr) where

import Types
import Control.Category as Cat
import Control.Monad.Except
import Control.Monad.State
import Data.Functor
import Data.Functor.Identity
import Control.Applicative as Ap
import Data.Text as T
import Data.List as L
import Data.Coerce
import Debug.Trace
import Data.Attoparsec.Text as P
import Data.Set as S

charBracketStart = '('
charBracketEnd   = ')'
charImplies      = '→'
charAnd          = '∧'
charOr           = '∨'
charNot          = '￢'
charBottom       = '⊥'
nonVarChars = [
      charBracketStart
    , charBracketEnd  
    , charImplies     
    , charAnd         
    , charOr          
    , charNot         
    , charBottom      
  ]
isVarChar = \case
  '(' -> False
  ')' -> False
  '→' -> False
  '∧' -> False
  '∨' -> False
  '￢' -> False
  '⊥' -> False
  ' '  -> False
  '\n' -> False
  '\t' -> False
  '\0' -> False
  _    -> True
  

altsImplies = ["->", "to"]
altsAnd = ["and", "&&", "/\\"]
altsOr  = ["or" , "||", "\\/"]
altsNot = ["~" , "!", "¬", "not"]
altsBottom = ["×", "bot"]

isWhiteSpace :: Char -> Bool
isWhiteSpace char =
  case char of
  ' '  -> True
  '\n' -> True
  '\t' -> True
  _  -> False


tshow :: Show a => a -> Text
tshow = show >>> T.pack


stringToExpr :: Text -> Either Text Expr
stringToExpr =
  let parseVar :: Parser Expr
      parseVar = 
        P.skipSpace *> (
              (P.char charBottom $> ExprBottom)
          <|> (ExprVar <$> P.takeWhile1 isVarChar)
        )

      parseParen :: Parser Expr
      parseParen = (char charBracketStart *> parseExpr <* char charBracketEnd) <|> parseVar

      parseNot :: Parser Expr
      parseNot = ((`Implies` ExprBottom) <$ (char charNot <* P.skipSpace) <*> parseParen) <|> parseParen

      parseInfixL op opchar parser =
        let go e =     (go =<< (op e <$ (P.skipSpace <* char opchar *> P.skipSpace) <*> parser))
                   <|> pure e
        in go =<< parser
      
      parseInfixR op opchar parser =
        let go e =     (op e <$ (P.skipSpace <* char opchar *> P.skipSpace) <*> (go =<< parser))
                   <|> pure e
        in go =<< parser

      parseAnd :: Parser Expr
      parseAnd = parseInfixL And charAnd parseNot

      parseOr :: Parser Expr
      parseOr = parseInfixL Or charOr parseAnd

      parseImplies :: Parser Expr
      parseImplies = parseInfixR Implies charImplies parseOr

      parseExpr = parseImplies

  in (<> (T.singleton '\0')) >>>
          ( flip (Prelude.foldl (\str from -> T.replace from (T.singleton charImplies) str)) altsImplies
        >>> flip (Prelude.foldl (\str from -> T.replace from (T.singleton charAnd    ) str)) altsAnd
        >>> flip (Prelude.foldl (\str from -> T.replace from (T.singleton charOr     ) str)) altsOr
        >>> flip (Prelude.foldl (\str from -> T.replace from (T.singleton charNot    ) str)) altsNot
        >>> flip (Prelude.foldl (\str from -> T.replace from (T.singleton charBottom ) str)) altsBottom
     )  >>> P.parse parseExpr >>> P.eitherResult >>> (\case; Left s -> Left (pack s); Right e -> Right e)
