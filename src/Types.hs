{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MagicHash #-}

module Types (
    TypeVar(..),
    Expr(..),
    TextExpr(..),
    LambdaVar(..),
    Proof(..),
    toTextExpr,
    toNomalExpr
  ) where

import Data.Text
import GHC.Stack
import qualified Data.List as L
import Data.Hashable
import Data.Text.Encoding
import Crypto.Hash.MD5 as MD5
import qualified Data.ByteString as BS
import Data.Map as M
import Data.Maybe
import GHC.Prim 
import GHC.Types 

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

data TextExpr =
    TextExprVar Text
  | TextExprBottom
  | TextImplies TextExpr TextExpr
  | TextAnd TextExpr TextExpr
  | TextOr TextExpr TextExpr
  deriving (Eq, Ord)

instance Hashable Expr where
  hashWithSalt (I# salt) expr = I# (lcgs (hashWithSalt' salt expr))

lcgs i =
  (48271# *# i) `remInt#` 0xffff#

hashWithSalt' :: Int# -> Expr -> Int#
hashWithSalt' salt expr =
  case expr of
    ExprVar (I# t) -> lcgs (salt +# t) -- case MD5.hash ( t) of hash -> fromIntegral (BS.index hash 0) + fromIntegral (BS.index hash 1) * 256 + fromIntegral (BS.index hash 2) * 65536 + fromIntegral (BS.index hash 3) * 16777216  
    ExprBottom     -> lcgs salt
    Implies e1 e2  -> lcgs (hashWithSalt' salt e1 *# 5# +# hashWithSalt' salt e2) *# 3# +# 0#
    And     e1 e2  -> lcgs (hashWithSalt' salt e1 *# 5# +# hashWithSalt' salt e2) *# 3# +# 1#
    Or      e1 e2  -> lcgs (hashWithSalt' salt e1 *# 5# +# hashWithSalt' salt e2) *# 3# +# 2#

instance Show Expr where
  show ExprBottom = "⊥"
  show (ExprVar tv) = show tv

  show (Implies (ExprVar v1) (ExprVar v2))    =        show (ExprVar v1) <>  " → "  <> show (ExprVar v2)
  show (Implies          t1  (ExprVar v2))    = "(" <> show          t1  <> ") → "  <> show (ExprVar v2)
  show (Implies (ExprVar v1) (Implies t2 t3)) =        show (ExprVar v1) <>  " → "  <> show (Implies t2 t3)
  show (Implies (ExprVar v1)          t2 )    =        show (ExprVar v1) <>  " → (" <> show          t2     <> ")"
  show (Implies          t1           t2 )    = "(" <> show          t1  <> ") → (" <> show          t2     <> ")"

  show (And (ExprVar v1) (ExprVar v2))    =        show (ExprVar v1) <>  " ∧ "  <> show (ExprVar v2)
  show (And (And t1 t3)  (ExprVar v2))    =        show (And t1 t3)  <>  " ∧ "  <> show (ExprVar v2)
  show (And          t1  (ExprVar v2))    = "(" <> show          t1  <> ") ∧ "  <> show (ExprVar v2)
  show (And (ExprVar v1) (And t2 t3) )    =        show (ExprVar v1) <>  " ∧ "  <> show (And t2 t3)
  show (And (ExprVar v1)          t2 )    =        show (ExprVar v1) <>  " ∧ (" <> show          t2     <> ")"
  show (And (And t1 t2)  (And t3 t4) )    =        show (And t1 t2)  <>  " ∧ "  <> show (And t3 t4)
  show (And          t1           t2 )    = "(" <> show          t1  <> ") ∧ (" <> show          t2     <> ")"

  show (Or  (ExprVar v1) (ExprVar v2))    =        show (ExprVar v1) <>  " ∨ "  <> show (ExprVar v2)
  show (Or  (Or  t1 t3)  (ExprVar v2))    =        show (Or  t1 t3)  <>  " ∨ "  <> show (ExprVar v2)
  show (Or           t1  (ExprVar v2))    = "(" <> show          t1  <> ") ∨ "  <> show (ExprVar v2)
  show (Or  (ExprVar v1) (Or  t2 t3) )    =        show (ExprVar v1) <>  " ∨ "  <> show (Or  t2 t3)
  show (Or  (ExprVar v1)          t2 )    =        show (ExprVar v1) <>  " ∨ (" <> show          t2     <> ")"
  show (Or  (Or  t1 t2)  (Or  t3 t4) )    =        show (Or  t1 t2)  <>  " ∨ "  <> show (Or  t3 t4)
  show (Or           t1           t2 )    = "(" <> show          t1  <> ") ∨ (" <> show          t2     <> ")"

showExprWithPars t =
  case t of
    ExprVar _ -> show t
    _         -> "(" <> show t <> ")"


data LambdaVar = LambdaVar Text Expr deriving Eq
instance Show LambdaVar where
  show (LambdaVar x _) = unpack x

data Proof =
    ProofVar LambdaVar
  | ProofAbs LambdaVar Proof
  | ProofApp Proof Proof
  | BuiltInTuple  Expr Expr
  | BuiltInFst    Expr Expr
  | BuiltInSnd    Expr Expr
  | BuiltInEither Expr Expr Expr
  | BuiltInLeft   Expr Expr
  | BuiltInRight  Expr Expr
  | BuiltInAbsurd Expr

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




toNomalExpr :: TextExpr -> (Expr, Map Int Text)
toNomalExpr expr =
  let toNomalExpr' :: TextExpr -> Int -> Map Text Int -> Map Int Text -> (Expr, Int, Map Text Int, Map Int Text)
      toNomalExpr' t i m revm =
        case t of
          TextExprBottom -> (ExprBottom, i, m, revm)

          TextExprVar tv ->
            case M.lookup tv m of
              Nothing -> (ExprVar (i+1), i+1, M.insert tv (i+1) m, M.insert (i+1) tv revm)
              Just j  -> (ExprVar j, j,  m, revm)

          TextAnd t1 t2 ->
            let (e1, i' , m' , revm' ) = toNomalExpr' t1 i  m  revm
                (e2, i'', m'', revm'') = toNomalExpr' t2 i' m' revm'
            in  (And e1 e2, i'', m'', revm'')

          TextOr t1 t2 ->
            let (e1, i' , m' , revm' ) = toNomalExpr' t1 i  m  revm
                (e2, i'', m'', revm'') = toNomalExpr' t2 i' m' revm'
            in  (Or e1 e2, i'', m'', revm'')

          TextImplies t1 t2 ->
            let (e1, i' , m' , revm' ) = toNomalExpr' t1 i  m  revm
                (e2, i'', m'', revm'') = toNomalExpr' t2 i' m' revm'
            in  (Implies e1 e2, i'', m'', revm'')
  in case toNomalExpr' expr 1 M.empty M.empty of (expr', _, _, revm) -> (expr', revm)

toTextExpr :: M.Map Int Text -> Expr -> TextExpr
toTextExpr revm expr =
  case expr of
    ExprBottom     -> TextExprBottom
    ExprVar i      -> TextExprVar $ fromMaybe "ERROR!" (M.lookup i revm)
    And     e1 e2  -> TextAnd (toTextExpr revm e1) (toTextExpr revm e2)
    Or      e1 e2  -> TextOr  (toTextExpr revm e1) (toTextExpr revm e2)
    Implies e1 e2  -> TextAnd (toTextExpr revm e1) (toTextExpr revm e2)