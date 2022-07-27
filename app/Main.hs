{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase #-}
module Main where

import Types
import Solver
import Printer
import Parser2

import Data.Text
import Control.Category
import Data.Functor.Identity
import Control.Monad.Except
import Control.Monad.Trans.Except
import GHC.IO.Handle (hSetBuffering)
import System.IO
import qualified Data.Text.IO as TIO
import System.Environment

main :: IO ()
main = 
  getArgs >>= (\case
      "-v":a:_  -> main'''' (pack a)
      "-l":a:_  -> mainl    (pack a)
      "-lv":a:_ -> main'    (pack a)
      a:_ -> main''''' (pack a)
      []  -> TIO.putStrLn "usage: ipc-hs [logic expression]"
    )


withLog :: Text -> IO (Either Text Proof)
withLog str = runExceptT (tryProve TIO.putStrLn =<< except (stringToExpr str))
withOutLog :: Text -> IO (Either Text Proof)
withOutLog str = pure $ runIdentity $ runExceptT (tryProve (const (Identity ())) =<< except (stringToExpr str))
main'     str = either TIO.putStrLn (showWithIndent    >>>    putStrLn) =<< withLog str
main''    str = either TIO.putStrLn (toProofTree       >>>TIO.putStrLn) =<< withLog str
main'''   str = either TIO.putStrLn (toProofTree2      >>>TIO.putStrLn) =<< withLog str
main''''  str = either TIO.putStrLn (toProofTree_cm_ayf>>>TIO.putStrLn) =<< withLog str
main''''' str = either TIO.putStrLn (toProofTree_cm_ayf>>>TIO.putStrLn) =<< withOutLog str
mainl     str = either TIO.putStrLn (showWithIndent    >>>    putStrLn) =<< withOutLog str