{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Parser (stringToHashedExpr) where

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

data Token =
    TokenBracketStart
  | TokenBracketEnd
  | TokenImplies
  | TokenAnd
  | TokenOr
  | TokenNot
  | TokenVar Text
  | TokenBottom
  deriving (Eq)

instance Show Token where
  show x = unpack $
    case x of
      TokenBracketStart -> strBracketStart
      TokenBracketEnd   -> strBracketEnd
      TokenImplies      -> strImplies
      TokenAnd          -> strAnd
      TokenOr           -> strOr
      TokenNot          -> strNot
      TokenVar x        -> x
      TokenBottom       -> strBottom

strBracketStart = "("
strBracketEnd   = ")"
strImplies      = "→"
strAnd          = "∧"
strOr           = "∨"
strNot          = "￢"
strBottom       = "⊥"

altsImplies = ["->", "to"]
altsAnd = ["and", "&&", "/\\"]
altsOr  = ["or" , "||", "\\/"]
altsNot = ["~" , "!", "¬"]
altsBottom = ["×", "bot"]

isWhiteSpace :: Char -> Bool
isWhiteSpace char =
  case char of
  ' '  -> True
  '\n' -> True
  '\t' -> True
  _  -> False

stringToTokens :: Text -> [Token]
stringToTokens string =
  let addVar vname tokens =
        case vname of
          "" -> tokens
          _  -> TokenVar vname : tokens

      readTokens reading tokens str =
        case T.uncons str of
          Nothing -> addVar reading tokens
          Just (c, t)
            | isWhiteSpace c -> readTokens "" (addVar reading tokens) (T.dropWhile isWhiteSpace str)
            | otherwise ->
              let mt = foldM (\b (symbol, token) ->
                        case T.stripPrefix symbol str of
                          Just next -> Left (token, next)
                          Nothing   -> Right ()
                    ) () [  (strBracketStart, TokenBracketStart)
                          , (strBracketEnd  , TokenBracketEnd)
                          , (strImplies     , TokenImplies)
                          , (strAnd         , TokenAnd)
                          , (strOr          , TokenOr)
                          , (strNot         , TokenNot)
                          , (strBottom      , TokenBottom)
                          ]
              in case mt of
                Left (token, next) -> readTokens "" (token : addVar reading tokens) next
                _                  -> readTokens (reading <> T.singleton c) tokens t
  in L.reverse $ readTokens "" []
      $ (    flip (Prelude.foldl (\str from -> T.replace from strImplies str)) altsImplies
         >>> flip (Prelude.foldl (\str from -> T.replace from strAnd     str)) altsAnd
         >>> flip (Prelude.foldl (\str from -> T.replace from strOr      str)) altsOr
         >>> flip (Prelude.foldl (\str from -> T.replace from strNot     str)) altsNot
         >>> flip (Prelude.foldl (\str from -> T.replace from strBottom  str)) altsBottom
        ) string

tshow :: Show a => a -> Text
tshow = show >>> T.pack

type MyParserM = StateT [Token] (ExceptT Text Identity)
  --deriving (Functor, Applicative, Monad, Alternative, MonadPlus, MonadState [Token], MonadError Str)

consume :: Token -> MyParserM ()
consume t = do
  env <- get
  case L.uncons env of
    Just (x, xs)
      | x == t -> put xs
    _ -> throwError ("expected \"" <> tshow t <> "\"")


consumeCond :: (Token -> Bool) -> MyParserM Token
consumeCond cond = do
  env <- get
  case L.uncons env of
    Just (x, xs)
     | cond x  -> put xs >> pure x
     | otherwise -> throwError $ "unexpected token: " <> tshow x <> ""
    _ -> throwError "no token"

consumeSelect :: [(Token, a)] -> MyParserM a
consumeSelect ts = do
  env <- get
  case L.uncons env of
    Just (x, xs) ->
      case L.find (fst >>> (== x)) ts of
        Just (t, a) -> put xs >> pure a
        Nothing     -> throwError ("expected \"" <> tshow (fst <$> ts) <> "\"")
    _               -> throwError ("expected \"" <> tshow (fst <$> ts) <> "\"")

consumeInfixR :: Token -> MyParserM ()
consumeInfixR t = do
  env <- get
  case L.uncons env of
    Just (x, xs)
     | x == t -> put xs
    _ -> throwError ("expected \"" <> tshow t <> "\"")

data Operator =
    InfixR [(Token, HashedExpr -> HashedExpr -> HashedExpr)]
  | InfixL [(Token, HashedExpr -> HashedExpr -> HashedExpr)]
  | Prefix [(Token, HashedExpr -> HashedExpr)]

foldWithTail :: (a -> t -> [t] -> a) -> a -> [t] -> a
foldWithTail f initial xs = fst $ Prelude.foldl (\(acc, xs') x -> (f acc x (Prelude.tail xs') , Prelude.tail xs')) (initial, xs) xs

type InfixChain = ([(HashedExpr, HashedExpr -> HashedExpr -> HashedExpr)], HashedExpr)

tokensToHashedExpr =
  let operators :: [Operator]
      operators = [
            InfixR [(TokenImplies,hashedImplies)]
          , InfixL [(TokenOr,hashedOr),(TokenAnd,hashedAnd)]
          , Prefix [(TokenNot, (`hashedImplies` hashedExprBottom))]
        ]

      parseVar :: MyParserM Text
      parseVar = do
        env <- get
        case L.uncons env of
          Just (TokenVar v, xs) -> put xs >> pure v
          _ -> throwError "not a variable"


      parseBracket :: MyParserM HashedExpr
      parseBracket =
        consume TokenBracketStart *> parseHashedExpr operators <* consume TokenBracketEnd

      parseInfixChain :: [(Token, HashedExpr -> HashedExpr -> HashedExpr)] -> [Operator] -> MyParserM InfixChain
      parseInfixChain os ops = 
        ((\e f (es, ex) -> ((e, f) : es, ex)) <$> parseHashedExpr ops <*> consumeSelect os <*> parseInfixChain os ops) <|>
        (([], ) <$> parseHashedExpr ops)


      chainToHashedExprInfixR :: InfixChain -> HashedExpr
      chainToHashedExprInfixR (es, ex) = L.foldr (\(e1,f) e2 -> f e1 e2) ex es

      chainToHashedExprInfixL :: InfixChain -> HashedExpr
      chainToHashedExprInfixL (es, ex) = L.foldl (\f (e2, f')-> f' (f e2)) Cat.id es ex

      parseHashedExpr :: [Operator] -> MyParserM HashedExpr
      parseHashedExpr ops =
        (case L.uncons ops of
          Just (op, ops') -> 
            case op of
              InfixR os -> chainToHashedExprInfixR <$> parseInfixChain os ops'
              InfixL os -> chainToHashedExprInfixL <$> parseInfixChain os ops'
              Prefix os -> consumeSelect os  <*> parseHashedExpr (op:ops')
          Nothing -> Ap.empty
        ) <|>
        parseBracket <|>
        (hashedExprBottom <$ consume TokenBottom) <|>
        (hashedExprVar <$> parseVar)

  in runMyParserM (parseHashedExpr operators)


runMyParserM :: MyParserM a -> [Token] -> Either Text a
runMyParserM x tokens =
  case runIdentity $ runExceptT $ runStateT x tokens of
    Right (result, []  ) -> Right result
    Right (result, t:ts) -> Left $ "unexpected token " <> tshow t <> ""
    Left  err      -> Left err

stringToHashedExpr :: Text -> Either Text HashedExpr
stringToHashedExpr = stringToTokens >>> tokensToHashedExpr
