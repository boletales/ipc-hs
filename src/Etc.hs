{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Etc () where

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
import qualified Data.Text.IO as TIO
import System.Random
import Control.Monad

generateExprs 0 =
  pure $ [hashedExprBottom] <> ((T.singleton >>> hashedExprVar) <$> "ABCDE")

generateExprs i = do
  mini <- generateExprs (i-1)
  mini1 <- selectRandom (3 * i) mini
  mini2 <- selectRandom (3 * i) mini
  mini3 <- selectRandom (3 * i) mini
  mini4 <- selectRandom (3 * i) mini
  mini5 <- selectRandom (5 * i) mini
  mini6 <- selectRandom (5 * i) mini
  
  pure ((hashedAnd     <$> mini1 <*> mini2)
     <> (hashedOr      <$> mini3 <*> mini4)
     <> (hashedImplies <$> mini5 <*> mini6)
     <>  mini)

selectRandom i xs =
  filterM (\_ -> (<i) <$> randomRIO (0, L.length xs)) xs