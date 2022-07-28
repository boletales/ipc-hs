{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MagicHash #-}

module Types (
    TypeVar(..),
    HashedExpr(..),
    TextExpr(..),
    LambdaVar(..),
    Proof(..),
    hashedExprToTextExpr,
    textExprtoHashedExpr,
    hashedExprVar,
    hashedExprBottom,
    hashedImplies,
    hashedAnd,
    hashedOr,
    getHash
  ) where

import Data.Text
import GHC.Stack
import qualified Data.List as L
import Data.Map as M
import Data.Maybe

data TypeVar =
  TypeVar Text |
  Bottom
  deriving (Eq, Ord)

instance Show TypeVar where
  show (TypeVar t) = unpack t
  show Bottom = "⊥"

data Expr =
    ExprVar Int
  | ExprBottom
  | Implies Expr Expr
  | And Expr Expr
  | Or Expr Expr
  deriving (Eq, Ord)

data HashedExpr =
    HashedExprVar    Int Int
  | HashedExprBottom Int
  | HashedImplies    Int HashedExpr HashedExpr
  | HashedAnd        Int HashedExpr HashedExpr
  | HashedOr         Int HashedExpr HashedExpr
  deriving (Eq, Ord)

lcgs i =
  (48271 * i) `rem` 0xffff

{-# INLINE getHash #-}
getHash e =
  case e of
    HashedExprVar    h _   -> h
    HashedExprBottom h     -> h
    HashedImplies    h _ _ -> h
    HashedAnd        h _ _ -> h
    HashedOr         h _ _ -> h

hashedExprSalt = 38516
hashedExprVar v     = HashedExprVar    (lcgs (v + hashedExprSalt)) v
hashedExprBottom    = HashedExprBottom (lcgs (0 + hashedExprSalt))
hashedImplies e1 e2 = HashedImplies    (lcgs (getHash e1 * 5 + getHash e2 * 3 + 0)) e1 e2
hashedAnd     e1 e2 = HashedAnd        (lcgs (getHash e1 * 5 + getHash e2 * 3 + 1)) e1 e2
hashedOr      e1 e2 = HashedOr         (lcgs (getHash e1 * 5 + getHash e2 * 3 + 2)) e1 e2

data TextExpr =
    TextExprVar Text
  | TextExprBottom
  | TextImplies TextExpr TextExpr
  | TextAnd TextExpr TextExpr
  | TextOr TextExpr TextExpr
  deriving (Eq, Ord)

<<<<<<< HEAD
instance Show Expr where
  show ExprBottom = "⊥"
  show (ExprVar tv) = show tv
=======
instance Hashable HashedExpr where
  hashWithSalt salt expr = getHash expr + salt
{-


hashWithSalt' :: Int# -> Expr -> Int#
hashWithSalt' salt expr =
  case expr of
    ExprVar (I# t) -> lcgs (salt +# t) -- case MD5.hash ( t) of hash -> fromIntegral (BS.index hash 0) + fromIntegral (BS.index hash 1) * 256 + fromIntegral (BS.index hash 2) * 65536 + fromIntegral (BS.index hash 3) * 16777216  
    ExprBottom     -> lcgs salt
    Implies e1 e2  -> lcgs (hashWithSalt' salt e1 *# 5# +# hashWithSalt' salt e2) *# 3# +# 0#
    And     e1 e2  -> lcgs (hashWithSalt' salt e1 *# 5# +# hashWithSalt' salt e2) *# 3# +# 1#
    Or      e1 e2  -> lcgs (hashWithSalt' salt e1 *# 5# +# hashWithSalt' salt e2) *# 3# +# 2#
-}

instance Show HashedExpr where
  show (HashedExprBottom _) = "⊥"
  show (HashedExprVar _ tv) = show tv
>>>>>>> feature/hash

  show (HashedImplies _ (HashedExprVar h1 v1) (HashedExprVar h2 v2))    =        show (HashedExprVar h1 v1) <>  " → "  <> show (HashedExprVar h2 v2)
  show (HashedImplies _                t1     (HashedExprVar h2 v2))    = "(" <> show                   t1  <> ") → "  <> show (HashedExprVar h2 v2)
  show (HashedImplies _ (HashedExprVar h1 v1) (HashedImplies h2 t2 t3)) =        show (HashedExprVar h1 v1) <>  " → "  <> show (HashedImplies h2 t2 t3)
  show (HashedImplies _ (HashedExprVar h1 v1)                   t2 )    =        show (HashedExprVar h1 v1) <>  " → (" <> show                t2     <> ")"
  show (HashedImplies _                t1                       t2 )    = "(" <> show                   t1  <> ") → (" <> show                t2     <> ")"

  show (HashedAnd _ (HashedExprVar h1 v1) (HashedExprVar h2 v2))    =        show (HashedExprVar h1 v1) <>  " ∧ "  <> show (HashedExprVar h2 v2)
  show (HashedAnd _ (HashedAnd h1 t1 t3)  (HashedExprVar h2 v2))    =        show (HashedAnd h1 t1 t3)  <>  " ∧ "  <> show (HashedExprVar h2 v2)
  show (HashedAnd _                  t1   (HashedExprVar h2 v2))    = "(" <> show               t1      <> ") ∧ "  <> show (HashedExprVar h2 v2)
  show (HashedAnd _ (HashedExprVar h1 v1) (HashedAnd h2 t2 t3) )    =        show (HashedExprVar h1 v1) <>  " ∧ "  <> show (HashedAnd h2 t2 t3)
  show (HashedAnd _ (HashedExprVar h1 v1)               t2     )    =        show (HashedExprVar h1 v1) <>  " ∧ (" <> show               t2     <> ")"
  show (HashedAnd _ (HashedAnd h1 t1 t2)  (HashedAnd h2 t3 t4) )    =        show (HashedAnd h1 t1 t2)  <>  " ∧ "  <> show (HashedAnd h2 t3 t4)
  show (HashedAnd _                t1                 t2 )          = "(" <> show               t1      <> ") ∧ (" <> show               t2     <> ")"

  show (HashedOr _ (HashedExprVar h1 v1) (HashedExprVar h2 v2))    =        show (HashedExprVar h1 v1) <>  " ∨ "  <> show (HashedExprVar h2 v2)
  show (HashedOr _ (HashedOr h1  t1 t3)  (HashedExprVar h2 v2))    =        show (HashedOr h1  t1 t3)  <>  " ∨ "  <> show (HashedExprVar h2 v2)
  show (HashedOr _                t1     (HashedExprVar h2 v2))    = "(" <> show               t1      <> ") ∨ "  <> show (HashedExprVar h2 v2)
  show (HashedOr _ (HashedExprVar h1 v1) (HashedOr h2  t2 t3) )    =        show (HashedExprVar h1 v1) <>  " ∨ "  <> show (HashedOr h2  t2 t3)
  show (HashedOr _ (HashedExprVar h1 v1)                t2    )    =        show (HashedExprVar h1 v1) <>  " ∨ (" <> show               t2     <> ")"
  show (HashedOr _ (HashedOr h1  t1 t2 ) (HashedOr h2  t3 t4) )    =        show (HashedOr h1  t1 t2)  <>  " ∨ "  <> show (HashedOr h2  t3 t4)
  show (HashedOr _               t1                    t2     )    = "(" <> show           t1          <> ") ∨ (" <> show               t2     <> ")"

showExprWithPars t =
  case t of
    HashedExprVar _ _ -> show t
    _                 -> "(" <> show t <> ")"


data LambdaVar = LambdaVar Text HashedExpr deriving Eq
instance Show LambdaVar where
  show (LambdaVar x _) = unpack x

data Proof =
    ProofVar LambdaVar
  | ProofAbs LambdaVar Proof
  | ProofApp Proof Proof
  | BuiltInTuple  HashedExpr HashedExpr
  | BuiltInFst    HashedExpr HashedExpr
  | BuiltInSnd    HashedExpr HashedExpr
  | BuiltInEither HashedExpr HashedExpr HashedExpr
  | BuiltInLeft   HashedExpr HashedExpr
  | BuiltInRight  HashedExpr HashedExpr
  | BuiltInAbsurd HashedExpr

instance Show Proof where
  show (ProofVar (LambdaVar n t)) = unpack n
  show (ProofAbs (LambdaVar n t) p) = "(\\" <> unpack n <> "::" <> showExprWithPars t <> " -> " <> show p <> ")"
  show (ProofApp (ProofApp p1 p2) p3) = "(" <> show p1 <> " " <> show p2 <> " " <> show p3 <> ")"
  show (ProofApp p1 p2) = "(" <> show p1 <> " " <> show p2 <> ")"
  show (BuiltInTuple  t1 t2   ) = "tuple_{" <> show t1 <> "},{"<>show t2<>"}"
  show (BuiltInFst    t1 t2   ) = "fst_{" <> show t1 <> "},{"<>show t2<>"}"
  show (BuiltInSnd    t1 t2   ) = "snd_{" <> show t1 <> "},{"<>show t2<>"}"
  show (BuiltInEither t1 t2 t3) = "either_{" <> show t1 <> "},{"<>show t2<>"},{"<>show t3<>"}"
  show (BuiltInLeft   t1 t2   ) = "left_{" <> show t1 <> "},{"<>show t2<>"}"
  show (BuiltInRight  t1 t2   ) = "right_{" <> show t1 <> "},{"<>show t2<>"}"
  show (BuiltInAbsurd t1      ) = "absurd_{" <> show t1 <> "}"

textExprtoHashedExpr :: TextExpr -> (HashedExpr, M.Map Int Text)
textExprtoHashedExpr expr =
  let textExprtoHashedExpr' :: TextExpr -> Int -> M.Map Text Int -> M.Map Int Text -> (HashedExpr, Int, M.Map Text Int, M.Map Int Text)
      textExprtoHashedExpr' t i m revm =
        case t of
          TextExprBottom -> (hashedExprBottom, i, m, revm)

          TextExprVar tv ->
            case M.lookup tv m of
<<<<<<< HEAD
              Nothing -> (ExprVar (i+1), i+1, M.insert tv (i+1) m, M.insert (i+1) tv revm)
              Just j  -> (ExprVar j, i,  m, revm)
=======
              Nothing -> (hashedExprVar (i+1), i+1, M.insert tv (i+1) m, M.insert (i+1) tv revm)
              Just j  -> (hashedExprVar j, i,  m, revm)
>>>>>>> feature/hash

          TextAnd t1 t2 ->
            let (e1, i' , m' , revm' ) = textExprtoHashedExpr' t1 i  m  revm
                (e2, i'', m'', revm'') = textExprtoHashedExpr' t2 i' m' revm'
            in  (hashedAnd e1 e2, i'', m'', revm'')

          TextOr t1 t2 ->
            let (e1, i' , m' , revm' ) = textExprtoHashedExpr' t1 i  m  revm
                (e2, i'', m'', revm'') = textExprtoHashedExpr' t2 i' m' revm'
            in  (hashedOr e1 e2, i'', m'', revm'')

          TextImplies t1 t2 ->
<<<<<<< HEAD
            let (e1, i' , m' , revm' ) = toNomalExpr' t1 i  m  revm
                (e2, i'', m'', revm'') = toNomalExpr' t2 i' m' revm'
            in  (Implies e1 e2, i'', m'', revm'')
  in case toNomalExpr' expr 0 M.empty M.empty of (expr', _, _, revm) -> (expr', revm)
=======
            let (e1, i' , m' , revm' ) = textExprtoHashedExpr' t1 i  m  revm
                (e2, i'', m'', revm'') = textExprtoHashedExpr' t2 i' m' revm'
            in  (hashedImplies e1 e2, i'', m'', revm'')
  in case textExprtoHashedExpr' expr 1 M.empty M.empty of (expr', _, _, revm) -> (expr', revm)
>>>>>>> feature/hash

hashedExprToTextExpr :: M.Map Int Text -> HashedExpr -> TextExpr
hashedExprToTextExpr revm expr =
  case expr of
    HashedExprBottom _     -> TextExprBottom
    HashedExprVar _ i      -> TextExprVar $ fromMaybe "ERROR!" (M.lookup i revm)
    HashedAnd _     e1 e2  -> TextAnd (hashedExprToTextExpr revm e1) (hashedExprToTextExpr revm e2)
    HashedOr  _     e1 e2  -> TextOr  (hashedExprToTextExpr revm e1) (hashedExprToTextExpr revm e2)
    HashedImplies _ e1 e2  -> TextAnd (hashedExprToTextExpr revm e1) (hashedExprToTextExpr revm e2)
