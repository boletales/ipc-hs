{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Solver (tryProve) where

import Types
import Printer
import Data.Text as T
import Data.Map as M
import Data.Set as S
import Control.Monad.Trans.Except
import Control.Category
import Control.Monad
import Control.Monad.Trans
import GHC.Stack
import Data.Maybe
import Data.List as L
import Data.Functor.Identity

tshow :: Show a => a -> Text
tshow = show >>> pack

someFunc :: IO ()
someFunc = putStrLn "someFunc"

rightMostMatch :: Expr -> Expr -> Maybe [Expr]
rightMostMatch needle haystack =
  if haystack == needle then Just []
  else
    case haystack of
      Implies t1 t2 -> (t1:) <$> rightMostMatch needle t2
      _             -> Nothing

batchApplication :: Proof -> [Proof] -> Proof
batchApplication = Prelude.foldl ProofApp

cntToName :: Int -> Text
cntToName i =
  if i < 26
    then T.singleton $ ['a'..'z'] !! i
    else "t" <> tshow (i-25)

andToList :: (Expr, Proof) -> [(Expr, Proof)]
andToList (expr, prf) =
  case expr of
    ExprVar tv     -> [(expr, prf)]
    Implies ex ex' -> [(expr, prf)]
    And ex ex'     -> join [[(expr, prf)], andToList (ex, ProofApp (BuiltInFst ex ex') prf), andToList (ex', ProofApp (BuiltInSnd ex ex') prf)]
    Or  ex ex'     -> [(expr, prf)]

orToCandidates :: Expr -> Map Expr Proof -> [(Proof, [Expr])]
orToCandidates goal boundvars =
  catMaybes $
  (\(k, t) -> (t, ) <$> rightMostMatch goal k) <$> ((\(k, t) ->
    case k of
      Or e1 e2 -> [(Implies (Implies e1 goal) (Implies (Implies e2 goal) goal), ProofApp (BuiltInEither e1 e2 goal) t)]
      _        -> []
    ) =<< M.assocs boundvars)

{-# SPECIALIZE tryProve :: (Text -> IO ()) -> Expr -> ExceptT Text IO Proof #-}
{-# SPECIALIZE tryProve :: (Text -> Identity ()) -> Expr -> ExceptT Text Identity Proof #-}
tryProve :: forall m. Monad m => (Text -> m ()) -> Expr -> ExceptT Text m Proof
tryProve log' expr =
  let log  level t = lift (log' (T.replicate level "  " <> t))
      exit level t = log level t >> throwE (t <> "\n")

      searchFromKnownTerms varcnt level boundvars goal =
        case M.lookup goal boundvars of
          Just proof -> log  level ("found a known term " <> pack (showWithType proof)) >> pure proof
          Nothing    -> exit level ("could not find known terms with type " <> tshow goal)

      useFunctions :: Int -> Int -> Map Expr Proof -> Map Expr Int -> Expr -> [(Proof, [Expr])] -> ExceptT Text m Proof
      useFunctions varcnt level boundvars searching goal extrafunctions = do
        let candidates' =    (M.mapMaybeWithKey (\k t -> (t, ) <$> rightMostMatch goal k) >>> M.elems) boundvars
                         <> orToCandidates goal boundvars
                         <> [(BuiltInAbsurd goal ,[ExprVar Bottom])]
                         <> extrafunctions
        let candidates =
              L.filter (\(_, ts) -> goal `notElem` ts) $
                 L.filter (\(_, ts) -> not $ L.any (`M.member` searching) ts) candidates'
              <> L.filter (\(_, ts) ->       L.any (`M.member` searching) ts) candidates'
        result <-
          foldM (\result (term, argstype) ->
              case result of
                Just _  -> pure result
                Nothing ->
                  log level ("searching args for known term " <> pack (showWithType term)) >> catchE (do
                    argsproof <- mapM (go varcnt (level + 2)  boundvars searching) argstype
                    pure $ Just $ batchApplication term argsproof
                  ) (\e -> log level "failed" >> pure Nothing)
            ) Nothing candidates
        case result of
          Just proof -> log  level ("found a proof " <> pack (showWithType proof)) >> pure proof
          Nothing    -> exit level ("could not find a proof with type " <> tshow goal)

      go :: Int -> Int -> Map Expr Proof -> Map Expr Int -> Expr -> ExceptT Text m Proof
      go varcnt level boundvars searching' goal =
        if M.lookup goal searching' == Just (M.size searching')
        then exit (level-1) "loop detected, exit" else
          let searching = M.insert goal (M.size searching') searching'
          in  log (level-1) (tshow (M.size searching)  <> " subgoal : " <> tshow goal) >>
              case goal of
                Implies t1 t2 ->
                  catchE (searchFromKnownTerms varcnt level boundvars goal) (\e -> do
                    let newvar     = LambdaVar (cntToName varcnt) t1
                    let boundvars' = Prelude.foldl (\m (t, p) -> M.insert t p m) boundvars (andToList (t1, ProofVar newvar))
                    log level ("abstruction " <> T.pack (showWithType (ProofVar newvar)))
                    ProofAbs newvar <$> go (varcnt+1) (level + 1) boundvars' searching t2
                  )

                ExprVar a ->
                    catchE (searchFromKnownTerms varcnt level boundvars goal) (
                      \e -> useFunctions varcnt level boundvars searching goal []
                    )


                And t1 t2 ->
                    catchE (searchFromKnownTerms varcnt level boundvars goal) (
                      \e -> useFunctions varcnt level boundvars searching goal [(BuiltInTuple t1 t2, [t1, t2])]
                    )

                Or t1 t2 ->
                    catchE (searchFromKnownTerms varcnt level boundvars goal) (
                      \e -> useFunctions varcnt level boundvars searching goal [(BuiltInLeft t1 t2, [t1]), (BuiltInRight t1 t2, [t2])]
                    )
  in go 0 1 M.empty M.empty expr