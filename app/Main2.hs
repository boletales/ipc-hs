{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
module Main2 where

import Data.Text.IO as TIO
import System.Environment
import Data.Text as T
import Control.Category
import Lib

main :: IO ()
main = 
  getArgs >>= (\case
      f:_ -> TIO.readFile f >>= (T.splitOn "\n" >>> mapM mainOX) >>= const (pure ())
      []  -> TIO.putStrLn "usage: ipc-hs-exe2 [file]"
    )

