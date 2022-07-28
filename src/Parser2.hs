{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module Parser2 (stringToTextExpr) where

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
import Data.HashSet as S
import Data.HashMap.Lazy as M
import Data.Maybe

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


stringToTextExpr :: Text -> Either Text TextExpr
stringToTextExpr =
  let parseVar :: Parser TextExpr
      parseVar = 
        P.skipSpace *> (
              (P.char charBottom $> TextExprBottom)
          <|> (TextExprVar <$> P.takeWhile1 isVarChar)
        )

      parseParen :: Parser TextExpr
      parseParen = (char charBracketStart *> parseTextExpr <* char charBracketEnd) <|> parseVar

      parseNot :: Parser TextExpr
      parseNot = ((`TextImplies` TextExprBottom) <$ (char charNot <* P.skipSpace) <*> parseParen) <|> parseParen

      parseInfixL op opchar parser =
        let go e =     (go =<< (op e <$ (P.skipSpace <* char opchar *> P.skipSpace) <*> parser))
                   <|> pure e
        in go =<< parser
      
      parseInfixR op opchar parser =
        let go e =     (op e <$ (P.skipSpace <* char opchar *> P.skipSpace) <*> (go =<< parser))
                   <|> pure e
        in go =<< parser

      parseAnd :: Parser TextExpr
      parseAnd = parseInfixL TextAnd charAnd parseNot

      parseOr :: Parser TextExpr
      parseOr = parseInfixL TextOr charOr parseAnd

      parseImplies :: Parser TextExpr
      parseImplies = parseInfixR TextImplies charImplies parseOr

      parseTextExpr = parseImplies

  in (<> (T.singleton '\0')) >>>
          ( flip (Prelude.foldl (\str from -> T.replace from (T.singleton charImplies) str)) altsImplies
        >>> flip (Prelude.foldl (\str from -> T.replace from (T.singleton charAnd    ) str)) altsAnd
        >>> flip (Prelude.foldl (\str from -> T.replace from (T.singleton charOr     ) str)) altsOr
        >>> flip (Prelude.foldl (\str from -> T.replace from (T.singleton charNot    ) str)) altsNot
        >>> flip (Prelude.foldl (\str from -> T.replace from (T.singleton charBottom ) str)) altsBottom
     )  >>> P.parse parseTextExpr >>> P.eitherResult >>> (\case; Left s -> Left (pack s); Right e -> Right e)