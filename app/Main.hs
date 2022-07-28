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
import Data.Map as M
import Types

main :: IO ()
main = 
  getArgs >>= (\case
      "-v":a:_  -> main'''' (pack a)
      "-l":a:_  -> mainl    (pack a)
      "-lv":a:_ -> main'    (pack a)
      a:_ -> main''''' (pack a)
      []  -> TIO.putStrLn "usage: ipc-hs-exe [logic expression]"
    )


withLog :: (Text -> IO ()) -> (TextExpr -> Text -> IO ()) -> (TextExpr -> M.Map Int Text -> Proof -> IO ()) -> Text -> IO ()
withLog parseerror failed succeed str =
  case stringToTextExpr str of
    Left err -> parseerror err
    Right texpr -> do
      (expr, revmap, result) <- tryProve TIO.putStrLn texpr
      case result of
        Left err  -> failed texpr err
        Right prf -> succeed texpr revmap prf

withOutLog :: (Text -> IO ()) -> (TextExpr -> Text -> IO ()) -> (TextExpr -> M.Map Int Text -> Proof -> IO ()) -> Text -> IO ()
withOutLog parseerror failed succeed str =
  case stringToTextExpr str of
    Left err -> parseerror err
    Right texpr -> do
      let (expr, revmap, result) = runIdentity $ tryProve (const (Identity ())) texpr
      case result of
        Left err  -> failed texpr err
        Right prf -> succeed texpr revmap prf

main'     = withLog    TIO.putStrLn (\expr _ -> TIO.putStrLn ("failed to proof " <> showTypeText expr)) (\expr revmap prf -> TIO.putStrLn (showWithIndent     revmap prf))
main''    = withLog    TIO.putStrLn (\expr _ -> TIO.putStrLn ("failed to proof " <> showTypeText expr)) (\expr revmap prf -> TIO.putStrLn (toProofTree        revmap prf))
main'''   = withLog    TIO.putStrLn (\expr _ -> TIO.putStrLn ("failed to proof " <> showTypeText expr)) (\expr revmap prf -> TIO.putStrLn (toProofTree2       revmap prf))
main''''  = withLog    TIO.putStrLn (\expr _ -> TIO.putStrLn ("failed to proof " <> showTypeText expr)) (\expr revmap prf -> TIO.putStrLn (toProofTree_cm_ayf revmap prf))
main''''' = withOutLog TIO.putStrLn (\expr _ -> TIO.putStrLn ("failed to proof " <> showTypeText expr)) (\expr revmap prf -> TIO.putStrLn (toProofTree_cm_ayf revmap prf))
mainl     = withOutLog TIO.putStrLn (\expr _ -> TIO.putStrLn ("failed to proof " <> showTypeText expr)) (\expr revmap prf -> TIO.putStrLn (showWithIndent     revmap prf))