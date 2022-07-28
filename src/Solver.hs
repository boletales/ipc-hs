{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE BangPatterns #-}
 
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
import Debug.Trace
import Data.Functor.Identity
import Data.Bifunctor

tshow :: Show a => a -> Text
tshow = show >>> pack

someFunc :: IO ()
someFunc = putStrLn "someFunc"


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
    ExprBottom     -> [(expr, prf)]
    ExprVar tv     -> [(expr, prf)]
    Implies ex ex' -> [(expr, prf)]
    And ex ex'     -> join [[(expr, prf)], andToList (ex, ProofApp (BuiltInFst ex ex') prf), andToList (ex', ProofApp (BuiltInSnd ex ex') prf)]
    Or  ex ex'     -> [(expr, prf)]


rightMostMatch :: Expr -> Expr -> Maybe [Expr]
rightMostMatch needle haystack =
  if haystack == needle then Just []
  else
    case haystack of
      Implies t1 t2 -> (t1:) <$> rightMostMatch needle t2
      And t1 t2     -> rightMostMatch needle t1
      _             -> Nothing

data Direction =
    DirFst   Expr Expr
  | DirSnd  Expr Expr
  | DirEither Expr Expr Expr
  | DirApply deriving (Show, Eq)

getCandidates :: [Set Expr] -> Proof -> Expr -> Expr -> [(Proof, [Direction], [Expr])]
getCandidates searching term goal haystack =
  if haystack == goal then [(term, [], [])]
  else
    case haystack of
      Implies t1 t2 
        | not (S.member t1 (L.head searching))
                    ->    ((\(p, ds, ts) -> (p, DirApply     :ds, t1:ts)) <$> getCandidates searching term goal t2)
      And t1 t2     ->    ((\(p, ds, ts) -> (p, DirSnd t1 t2 :ds, ts   )) <$> getCandidates searching term goal t2)
                       <> ((\(p, ds, ts) -> (p, DirFst t1 t2 :ds, ts   )) <$> getCandidates searching term goal t1)
      Or  t1 t2     
        | not (S.member (Implies t1 goal) (L.head searching)) && not (S.member (Implies t2 goal) (L.head searching))
                    ->     [(term, [DirEither t1 t2 goal, DirApply, DirApply], [Implies t1 goal, Implies t2 goal])]
      _ -> []

batchApplicationWithDirection :: (Proof, [Direction], [Expr]) -> [Proof] -> Proof
batchApplicationWithDirection (p, ds, ex) ps =
  fst $ L.foldl (\(p', ps') dir ->
      case dir of
        DirApply       ->
          case ps' of
            p'':ps'' -> (ProofApp p' p'', ps'')
            []       -> error "What!? Not enough args given!!!!!"

        DirFst    t1 t2    -> (ProofApp (BuiltInFst    t1 t2   ) p', ps')
        DirSnd    t1 t2    -> (ProofApp (BuiltInSnd    t1 t2   ) p', ps')
        DirEither t1 t2 t3 -> (ProofApp (BuiltInEither t1 t2 t3) p', ps')
    ) (p, ps) ds

-- orToCandidates :: Expr -> Map Expr Proof -> [(Proof, [Direction], [Expr])]
-- orToCandidates goal boundvars =
--   (\(k, t) ->
--     case k of
--       Or e1 e2 -> getCandidates (ProofApp (BuiltInEither e1 e2 goal) t) goal (Implies (Implies e1 goal) (Implies (Implies e2 goal) goal))
--       _        -> []
--     ) =<< M.assocs boundvars

{-# SPECIALIZE tryProve :: (Text -> IO ()) -> TextExpr -> IO (Expr, M.Map Int Text, Either Text Proof) #-}
{-# SPECIALIZE tryProve :: (Text -> Identity ()) -> TextExpr -> Identity (Expr, M.Map Int Text, Either Text Proof) #-}
--{-# INLINE tryProve#-}
tryProve :: forall m. Monad m => (Text -> m ()) -> TextExpr -> m (Expr, M.Map Int Text, Either Text Proof)
tryProve log' expr =
  let log  level t = lift (log' (T.replicate level "  " <> t))
      exit level t = log level t >> throwE (t <> "\n")

      searchFromKnownTerms varcnt level boundvars goal =
        case M.lookup goal boundvars of
          Just proof -> log  level ("found a known term " <> pack (showWithType proof)) >> pure proof
          Nothing    -> exit level ("could not find known terms with type " <> tshow goal)

      useFunctions :: Int -> Int -> Map Expr Proof -> [Set Expr] -> Expr -> [(Proof, [Direction], [Expr])] -> ExceptT Text m Proof
      useFunctions varcnt level boundvars searching goal extrafunctions = do
        log level ("searching proofs with type " <> tshow goal)
        let candidates = 
                 (M.mapWithKey (\k t -> getCandidates searching t goal k) >>> M.elems >>> join) boundvars
              <> extrafunctions
              <> [(BuiltInAbsurd goal , [DirApply],[ExprBottom])]
              -- <> orToCandidates goal boundvars
        --let candidates =
        --      L.filter (\(_, _ ,ts) -> L.all (\t -> M.lookup t (L.head searching) /= Just (M.size boundvars)) ts) candidates'
              --    L.filter (\(_, ts) -> not $ L.any (`M.member` searching) ts) 
              -- <> L.filter (\(_, ts) ->       L.any (`M.member` searching) ts) candidates'
        result <-
          foldM (\result (term, direction, argstype) ->
              case result of
                Right _  -> pure result
                Left memo ->
                  log level ("searching args for known term " <> pack (showWithType term) <> ", " <> tshow argstype) >> catchE (do
                    (memo', revargs) <- foldM (\(memo', args) goal' ->
                        case M.lookup goal' memo' of
                          Just (Just p) -> log level ("already found " <> tshow goal') >> pure (memo', p:args)
                          Just Nothing  -> throwE memo'
                          Nothing ->
                            catchE (do
                                arg <- go varcnt (level + 2) boundvars (searching) goal'
                                pure (M.insert goal' (Just arg) memo', arg:args)
                              ) (\e ->
                                throwE (M.insert goal' Nothing memo')
                              )
                      ) (memo, []) argstype
                    pure $ Right $ batchApplicationWithDirection (term, direction, argstype) (L.reverse revargs)
                  ) (\e -> log level "failed" >> pure (Left e))
            ) (Left (M.map Just boundvars) ) candidates
        case result of
          Right proof -> log  level ("found a proof " <> pack (showWithType proof)) >> pure proof
          Left  memo  -> exit level ("could not find a proof with type " <> tshow goal)

      go :: Int -> Int -> Map Expr Proof -> [Set Expr] -> Expr -> ExceptT Text m Proof
      go varcnt level boundvars searching' goal =
        if S.member goal (L.head searching') 
        then exit (level-1) "loop detected, exit" else
          let searching = S.insert goal (L.head searching') : L.tail searching'
          in  log (level-1) (tshow (M.size boundvars)  <> " subgoal : " <> tshow goal ) >>
              case goal of
                Implies t1 t2 ->
                  catchE (searchFromKnownTerms varcnt level boundvars goal) (\e -> 
                    case t1 of
                      ExprBottom -> do
                        let newvar     = LambdaVar (cntToName varcnt) t1
                        log level ("abstruction " <> T.pack (showWithType (ProofVar newvar)) <> " (short cirquit: absurd)")
                        pure $ ProofAbs newvar (ProofApp (BuiltInAbsurd t2) (ProofVar newvar))
                      _ 
                       | otherwise -> do
                        let newvar     = LambdaVar (cntToName varcnt) t1
                        let boundvars' = Prelude.foldl (\m (t, p) -> M.insert t p m) boundvars (andToList (t1, ProofVar newvar))
                        let searching'' = if M.size boundvars == M.size boundvars' then searching else S.empty:searching
                        log level ("abstruction " <> T.pack (showWithType (ProofVar newvar)))
                        ProofAbs newvar <$> go (varcnt+1) (level + 1) boundvars' searching'' t2
                  )

                ExprBottom ->
                    catchE (searchFromKnownTerms varcnt level boundvars goal) (
                      \e -> useFunctions varcnt level boundvars searching goal []
                    )

                ExprVar a ->
                    catchE (searchFromKnownTerms varcnt level boundvars goal) (
                      \e -> useFunctions varcnt level boundvars searching goal []
                    )


                And t1 t2 ->
                    catchE (searchFromKnownTerms varcnt level boundvars goal) (
                      \e -> useFunctions varcnt level boundvars searching goal [(BuiltInTuple t1 t2, [DirApply, DirApply], [t1, t2])]
                    )

                Or t1 t2 ->
                    catchE (searchFromKnownTerms varcnt level boundvars goal) (
                      \e -> useFunctions varcnt level boundvars searching goal [(BuiltInLeft t1 t2, [DirApply], [t1]), (BuiltInRight t1 t2, [DirApply], [t2])]
                    )
  in (\(e, m) -> (e, m, ) <$> runExceptT (go 0 1 M.empty [S.empty] e)) (toNomalExpr expr)