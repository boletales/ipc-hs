{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}

module Solver (tryProve) where

import Types
import Printer
import Data.Text as T
import Data.IntMap as IM
import Data.IntSet as IS
import Data.Map as M
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
batchApplication = L.foldl' ProofApp

cntToName :: Int -> Text
cntToName i =
  if i < 26
    then T.singleton $ ['a'..'z'] !! i
    else "t" <> tshow (i-25)

andToList :: (HashedExpr, Proof) -> [(HashedExpr, Proof)]
andToList (expr, prf) =
  case expr of
    HashedExprBottom h     -> [(expr, prf)]
    HashedExprVar h tv     -> [(expr, prf)]
    HashedImplies h ex ex' -> [(expr, prf)]
    HashedAnd h ex ex'     -> join [[(expr, prf)], andToList (ex, ProofApp (BuiltInFst ex ex') prf), andToList (ex', ProofApp (BuiltInSnd ex ex') prf)]
    HashedOr  h ex ex'     -> [(expr, prf)]


rightMostMatch :: HashedExpr -> HashedExpr -> Maybe [HashedExpr]
rightMostMatch needle haystack =
  if haystack == needle then Just []
  else
    case haystack of
      HashedImplies h t1 t2 -> (t1:) <$> rightMostMatch needle t2
      HashedAnd h t1 t2     -> rightMostMatch needle t1
      _             -> Nothing

data Direction =
    DirFst   HashedExpr HashedExpr
  | DirSnd  HashedExpr HashedExpr
  | DirEither HashedExpr HashedExpr HashedExpr
  | DirApply deriving (Show, Eq)

getCandidates :: HashedExprSet -> HashedExprMap (HashedExpr, Proof) -> Proof -> HashedExpr -> HashedExpr -> [(Proof, [Direction], [HashedExpr])]
getCandidates searching boundvars term goal haystack =
  if haystack == goal then [(term, [], [])]
  else
    case haystack of
      HashedImplies h t1 t2
        | not (hsmember t1 searching)
                            ->    ((\(p, ds, ts) -> (p, DirApply     :ds, t1:ts)) <$> getCandidates searching boundvars term goal t2)
      HashedAnd h t1 t2     ->    ((\(p, ds, ts) -> (p, DirSnd t1 t2 :ds, ts   )) <$> getCandidates searching boundvars term goal t2)
                               <> ((\(p, ds, ts) -> (p, DirFst t1 t2 :ds, ts   )) <$> getCandidates searching boundvars term goal t1)
      HashedOr h t1 t2
        |    not (hsmember (hashedImplies t1 goal) searching) && not (hsmember (hashedImplies t2 goal) searching)
          && not (hmmember t1 boundvars) && not (hmmember t2 boundvars)
                    ->     [(term, [DirEither t1 t2 goal, DirApply, DirApply], [hashedImplies t1 goal, hashedImplies t2 goal])]
      _ -> []

batchApplicationWithDirection :: (Proof, [Direction], [HashedExpr]) -> [Proof] -> Proof
batchApplicationWithDirection (p, ds, ex) ps =
  fst $ L.foldl' (\(p', ps') dir ->
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


type HashedExprMap = IM.IntMap

{-# INLINE hminsert #-}
hminsert :: HashedExpr -> a -> HashedExprMap a -> HashedExprMap a
hminsert k = IM.insert (getHash k)

{-# INLINE hmsize #-}
hmsize :: HashedExprMap a -> Int
hmsize = IM.size

{-# INLINE hmmap #-}
hmmap :: (a -> b) -> HashedExprMap a -> HashedExprMap b
hmmap = IM.map

{-# INLINE hmlookup #-}
hmlookup :: HashedExpr -> HashedExprMap a -> Maybe a
hmlookup e = IM.lookup (getHash e)

{-# INLINE hmelems #-}
hmelems :: HashedExprMap a -> [a]
hmelems = IM.elems

{-# INLINE hmempty #-}
hmempty :: HashedExprMap a
hmempty = IM.empty

{-# INLINE hmmember #-}
hmmember :: HashedExpr -> HashedExprMap a -> Bool
hmmember e = IM.member (getHash e)

type HashedExprSet = IS.IntSet

{-# INLINE hsempty #-}
hsempty :: HashedExprSet
hsempty = IS.empty

{-# INLINE hsmember #-}
hsmember :: HashedExpr -> HashedExprSet -> Bool
hsmember e = IS.member (getHash e)

{-# INLINE hsinsert #-}
hsinsert :: HashedExpr -> HashedExprSet -> HashedExprSet
hsinsert e = IS.insert (getHash e)

{-
type HashedExprMap = HM.HashMap HashedExpr

{-# INLINE hminsert #-}
hminsert :: HashedExpr -> a -> HashedExprMap a -> HashedExprMap a
hminsert = HM.insert

{-# INLINE hmsize #-}
hmsize :: HashedExprMap a -> Int
hmsize = HM.size

{-# INLINE hmmap #-}
hmmap :: (a -> b) -> HashedExprMap a -> HashedExprMap b
hmmap = HM.map

{-# INLINE hmlookup #-}
hmlookup :: HashedExpr -> HashedExprMap a -> Maybe a
hmlookup = HM.lookup

{-# INLINE hmelems #-}
hmelems :: HashedExprMap a -> [a]
hmelems = HM.elems

{-# INLINE hmempty #-}
hmempty :: HashedExprMap a
hmempty = HM.empty

type HashedExprSet = HS.HashSet HashedExpr

{-# INLINE hsempty #-}
hsempty :: HashedExprSet
hsempty = HS.empty

{-# INLINE hsmember #-}
hsmember :: HashedExpr -> HashedExprSet -> Bool
hsmember = HS.member

{-# INLINE hsinsert #-}
hsinsert :: HashedExpr -> HashedExprSet -> HashedExprSet
hsinsert = HS.insert
-}


{-# SPECIALIZE tryProve :: (Text -> IO       ()) -> HashedExpr -> IO       (HashedExpr, Either Text Proof) #-}
{-# SPECIALIZE tryProve :: (Text -> Identity ()) -> HashedExpr -> Identity (HashedExpr, Either Text Proof) #-}
{-# INLINE tryProve #-}
tryProve :: forall m. Monad m => (Text -> m ()) -> HashedExpr -> m (HashedExpr, Either Text Proof)
tryProve log' expr =
  let log  level t = lift (log' (T.replicate level "  " <> t))
      --exit level t = log level t >> throwE (t <> "\n")

      {-# INLINE searchFromKnownTerms #-}
      searchFromKnownTerms :: Int -> Int -> HashedExprMap (HashedExpr, Proof) -> HashedExprMap (HashedExpr, Proof) -> HashedExprSet -> HashedExpr -> ExceptT HashedExprSet m Proof
      searchFromKnownTerms varcnt level boundvars auxvars searching goal =
        case hmlookup goal auxvars of
          Just (_, proof) -> log  level ("found a known term " <> pack (showWithType proof))           >> pure proof
          Nothing         -> log  level ("could not find known terms with type " <> showTypeText goal) >> throwE searching

      useFunctions :: Int -> Int -> HashedExprMap (HashedExpr, Proof) -> HashedExprMap (HashedExpr, Proof) -> HashedExprSet -> HashedExpr -> [(Proof, [Direction], [HashedExpr])] -> ExceptT HashedExprSet m Proof
      useFunctions varcnt level boundvars auxvars searching goal extrafunctions = {-# SCC useFunctions #-} do
        log level ("searching proofs with type " <> tshow goal)
        let !candidates =
                 (hmmap (\(k, t) -> getCandidates searching boundvars t goal k) >>> hmelems >>> join) boundvars
              <> L.filter (\(p, d, e) -> not (L.any (`hsmember` searching) e)) extrafunctions
              <> [(BuiltInAbsurd goal , [DirApply],[hashedExprBottom])]
              -- <> orToCandidates goal boundvars
        --let candidates =
        --      L.filter (\(_, _ ,ts) -> L.all (\t -> M.lookup t (L.head searching) /= Just (M.size boundvars)) ts) candidates'
              --    L.filter (\(_, ts) -> not $ L.any (`M.member` searching) ts) 
              -- <> L.filter (\(_, ts) ->       L.any (`M.member` searching) ts) candidates'

        result <-
          foldM (\result (term, direction, argstype) ->
              case result of
                Right _  -> pure result
                Left (memo, searching') ->
                  log level ("searching args for known term " <> pack (showWithType term) <> ", " <> tshow argstype) >> catchE (do
                    (memo', revargs) <- foldM (\(memo', args) goal' ->
                        case hmlookup goal' memo' of
                          Just (t, p) -> log level ("already found " <> tshow goal') >> pure (memo', p:args)
                          Nothing ->
                            if hsmember goal' searching' then throwE (memo', searching') else
                              catchE (do
                                  log level ("searching for " <> tshow goal')
                                  arg <- go varcnt (level + 2) boundvars memo' searching' goal'
                                  pure (hminsert goal' (goal', arg) memo', arg:args)
                                ) (\e ->
                                  throwE (memo', hsinsert goal' e)
                                )
                      ) (memo, []) argstype
                    pure $ Right $ batchApplicationWithDirection (term, direction, argstype) (L.reverse revargs)
                  ) (\e -> log level "failed" >> pure (Left e))
            ) (Left (auxvars, searching) ) candidates
        case result of
          Right proof -> log level ("found a proof " <> pack (showWithType proof))     >> pure proof
          Left  (memo, searching')  -> log level ("could not find a proof with type " <> tshow goal) >> throwE searching'

      go :: Int -> Int -> HashedExprMap (HashedExpr, Proof) -> HashedExprMap (HashedExpr, Proof) -> HashedExprSet -> HashedExpr -> ExceptT HashedExprSet m Proof
      go varcnt level boundvars auxvars searching' goal =
        if hsmember goal searching'
        then log (level-1) ("loop detected, exit : " <> showTypeText goal)  >> throwE searching' else
          let searching = hsinsert goal searching'
          in  log (level-1) (tshow (hmsize boundvars)  <> " subgoal : " <> showTypeText goal ) >>
              case goal of
                HashedImplies h t1 t2 ->
                  {-# SCC go_HashedImplies #-}
                  catchE (searchFromKnownTerms varcnt level boundvars auxvars searching goal) (\e ->
                    case t1 of
                      HashedExprBottom h' -> do
                        let newvar     = LambdaVar (cntToName varcnt) t1
                        log level ("abstruction " <> T.pack (showWithType (ProofVar newvar)) <> " (short cirquit: absurd)")
                        pure $ ProofAbs newvar (ProofApp (BuiltInAbsurd t2) (ProofVar newvar))
                      _
                       | otherwise -> do
                        let newvar     = LambdaVar (cntToName varcnt) t1
                        let boundvars' = L.foldl' (\m (t, p) -> hminsert t (t, p) m) boundvars (andToList (t1, ProofVar newvar))
                        let auxvars'   = L.foldl' (\m (t, p) -> hminsert t (t, p) m) auxvars   (andToList (t1, ProofVar newvar))
                        let searching'' = if hmsize boundvars == hmsize boundvars' then searching else hsempty
                        log level ("abstruction " <> T.pack (showWithType (ProofVar newvar)))
                        ProofAbs newvar <$> catchE (go (varcnt+1) (level + 1) boundvars' auxvars' searching'' t2) (throwE <<< IS.union searching)
                  )

                HashedExprBottom h ->
                    {-# SCC go_HashedExprBottom #-}
                    catchE (searchFromKnownTerms varcnt level boundvars auxvars searching goal) (
                      \e -> useFunctions varcnt level boundvars auxvars searching goal []
                    )

                HashedExprVar h a ->
                    {-# SCC go_HashedExprVar #-}
                    catchE (searchFromKnownTerms varcnt level boundvars auxvars searching goal) (
                      \e -> useFunctions varcnt level boundvars auxvars searching goal []
                    )


                HashedAnd h t1 t2 ->
                    {-# SCC go_HashedAnd #-}
                    catchE (searchFromKnownTerms varcnt level boundvars auxvars searching goal) (
                      \e -> useFunctions varcnt level boundvars auxvars searching goal [(BuiltInTuple t1 t2, [DirApply, DirApply], [t1, t2])]
                    )

                HashedOr h t1 t2 ->
                    {-# SCC go_HashedOr #-}
                    catchE (searchFromKnownTerms varcnt level boundvars auxvars searching goal) (
                      \e -> useFunctions varcnt level boundvars auxvars searching goal [(BuiltInLeft t1 t2, [DirApply], [t1]), (BuiltInRight t1 t2, [DirApply], [t2])]
                    )
  in (\e -> ((e, ) <<< first (const "failed to proof.")) <$> runExceptT (go 0 1 hmempty hmempty hsempty e)) expr