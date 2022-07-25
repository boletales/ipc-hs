{-# LANGUAGE OverloadedStrings  #-}
module Main where

import Types
import Solver
import Printer
import Parser

import Data.Text
import Control.Category
import Control.Monad.Except
import Control.Monad.Trans.Except
import qualified Data.Text.IO as TIO
import GHC.IO.Handle (hSetBuffering)
import System.IO

main :: IO ()
main = 
  hSetBuffering stdout NoBuffering >> hSetBuffering stdin LineBuffering >> 
  forever (TIO.putStr "ipc-hs> " >> TIO.getLine >>= main')

main' str = either (unpack>>>putStrLn) (showWithIndent>>>putStrLn) =<< runExceptT (tryProve (unpack>>>putStrLn) =<< except (stringToExpr str))
main'' str = either (unpack>>>putStrLn) (toProofTree>>>unpack>>>putStrLn) =<< runExceptT (tryProve (unpack>>>putStrLn) =<< except (stringToExpr str))
main''' str = either (unpack>>>putStrLn) (toProofTree2>>>unpack>>>putStrLn) =<< runExceptT (tryProve (unpack>>>putStrLn) =<< except (stringToExpr str))