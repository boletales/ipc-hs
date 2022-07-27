{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase #-}
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

main :: IO ()
main = 
  getArgs >>= (\case
      f:_ -> TIO.readFile f >>= (T.splitOn "\n" >>> mapM main''''') >>= (const (pure ()) {-sum >>> (\i -> TIO.putStrLn ("\n\nproved " <> pack (show i) <> " exprs"))-})
      []  -> TIO.putStrLn "usage: ipc-hs-exe2 [file]"
    )

--main''''' :: Text -> IO Int
--main''''' str = either (const $ TIO.putStrLn ("failed to prove: " <> str <> "\n") >> pure 0) (\r -> TIO.putStrLn (toProofTree_cm_ayf r) >> pure 1) $ runIdentity $ runExceptT (tryProve (const (Identity ())) =<< except (stringToExpr str))


main''''' :: Text -> IO Int
main''''' str = either (
    const $ TIO.putStrLn ("X\t" <> str) >> pure 0
    --const $ TIO.putStrLn ("~~\n" <> str <> "\nNot provable\n\n~~") >> pure 0
  ) (
    const $ TIO.putStrLn ("O\t" <> str) >> pure 0
    --const $ TIO.putStrLn ("~~\n" <> str <> "\nProvable\n\n~~") >> pure 0
  ) $ runIdentity $ runExceptT (tryProve (const (Identity ())) =<< except (stringToExpr str))