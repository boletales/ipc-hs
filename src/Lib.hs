{-# LANGUAGE OverloadedStrings  #-}
module Lib where

import Types
import Parser2
import Printer
import Solver
import Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Functor.Identity


withLog :: (Text -> IO ()) -> (HashedExpr -> Text -> IO ()) -> (HashedExpr -> Proof -> IO ()) -> Text -> IO ()
withLog parseerror failed succeed str =
  case stringToHashedExpr str of
    Left err -> parseerror err
    Right expr -> do
      (_, result) <- tryProve TIO.putStrLn expr
      case result of
        Left err  -> failed expr err
        Right prf -> succeed expr prf

withOutLog :: (Text -> IO ()) -> (HashedExpr -> Text -> IO ()) -> (HashedExpr -> Proof -> IO ()) -> Text -> IO ()
withOutLog parseerror failed succeed str =
  case stringToHashedExpr str of
    Left err -> parseerror err
    Right expr -> do
      let (_, result) = runIdentity $ tryProve (const (Identity ())) expr
      case result of
        Left err  -> failed expr err
        Right prf -> succeed expr prf


failedToProof :: HashedExpr -> p -> IO ()
failedToProof expr _ = TIO.putStrLn ("failed to proof " <> showTypeText expr)
mainlv :: Text -> IO ()
mainlv = withLog    TIO.putStrLn failedToProof (\expr prf -> TIO.putStrLn (showWithIndent prf))
mainv :: Text -> IO ()
mainv  = withLog    TIO.putStrLn failedToProof (\expr prf -> TIO.putStrLn (toProofTree_cm_ayf prf))
main' :: Text -> IO ()
main'  = withOutLog TIO.putStrLn failedToProof (\expr prf -> TIO.putStrLn (toProofTree_cm_ayf prf))
mainl :: Text -> IO ()
mainl  = withOutLog TIO.putStrLn failedToProof (\expr prf -> TIO.putStrLn (showWithIndent     prf))
maint :: Text -> IO ()
maint  = withOutLog TIO.putStrLn failedToProof (\expr prf -> TIO.putStrLn (toProofTree2 prf))


mainOX :: Text -> IO ()
mainOX str = 
  withOutLog (\pe -> TIO.putStrLn ("?\t" <> str)) (\expr err -> TIO.putStrLn ("X\t" <> str)) (\expr prf -> TIO.putStrLn ("O\t" <> str)) str