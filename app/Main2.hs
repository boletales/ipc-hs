{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
module Main2 where

import Types
import Solver
import Printer
import Parser2

import Data.Text as T
import Control.Category
import Data.Functor.Identity
import Control.Monad.Except
import Control.Monad.Trans.Except
import GHC.IO.Handle (hSetBuffering)
import System.IO
import qualified Data.Text.IO as TIO
import System.Environment
import Data.Foldable
import Data.Functor
import Data.Map as M
import Types

main :: IO ()
main = 
  getArgs >>= (\case
      f:_ -> TIO.readFile f >>= (T.splitOn "\n" >>> mapM main''''') >>= (const (pure ()) {-sum >>> (\i -> TIO.putStrLn ("\n\nproved " <> pack (show i) <> " exprs"))-})
      []  -> TIO.putStrLn "usage: ipc-hs-exe2 [file]"
    )

--main''''' :: Text -> IO Int
--main''''' str = either (const $ TIO.putStrLn ("failed to prove: " <> str <> "\n") >> pure 0) (\r -> TIO.putStrLn (toProofTree_cm_ayf r) >> pure 1) $ runIdentity $ runExceptT (tryProve (const (Identity ())) =<< except (stringToExpr str))

tshow :: Show a => a -> Text
tshow = show >>> pack

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

main''''' :: Text -> IO ()
main''''' str = 
  withOutLog (\pe -> TIO.putStrLn ("?\t" <> str)) (\expr err -> TIO.putStrLn ("X\t" <> str)) (\expr revmap prf -> TIO.putStrLn ("O\t" <> str)) str