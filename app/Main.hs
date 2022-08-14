{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase #-}
module Main where

import Data.Text.IO as TIO
import System.Environment
import Data.Text as T
import Lib
import Control.Category

main :: IO ()
main = 
  getArgs >>= (\case
      "-v":a:_  -> mainv  (pack a)
      "-l":a:_  -> mainl  (pack a)
      "-lv":a:_ -> mainlv (pack a)
      "-t":a:_  -> maint (pack a)
      "--bench":f:_ -> TIO.readFile f >>= (T.splitOn "\n" >>> mapM mainOX) >>= const (pure ())
      a:_       -> main'  (pack a)
      []  -> TIO.putStrLn "usage: ipc-hs-exe [logic expression]"
    )
