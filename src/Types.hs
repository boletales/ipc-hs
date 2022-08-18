{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}

module Types (
    TypeVar(..),
    HashedExpr(..),
    LambdaVar(..),
    Proof(..),
    hashedExprVar,
    hashedExprBottom,
    hashedImplies,
    hashedAnd,
    hashedOr,
    getHash,
    showTypeText
  ) where

import Data.Text
import GHC.Stack
import qualified Data.List as L
import Data.Map as M
import Data.Maybe
import Data.Text as T
import Data.Char
import Data.Bits
import Data.Hashable

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
    HashedExprVar    Int Text
  | HashedExprBottom Int
  | HashedImplies    Int HashedExpr HashedExpr
  | HashedAnd        Int HashedExpr HashedExpr
  | HashedOr         Int HashedExpr HashedExpr
  deriving (Eq, Ord)

instance Hashable HashedExpr where
  hashWithSalt salt e = getHash e + salt

xorshift :: Int -> Int
xorshift i0 =
  let !i1 = xor i0 (unsafeShiftL i0 13)
      !i2 = xor i1 (unsafeShiftR i1 7)
      !i3 = xor i2 (unsafeShiftL i2 17)
  in i3

{-# INLINE getHash #-}
getHash :: HashedExpr -> Int
getHash e =
  case e of
    HashedExprVar    h _   -> h
    HashedExprBottom h     -> h
    HashedImplies    h _ _ -> h
    HashedAnd        h _ _ -> h
    HashedOr         h _ _ -> h

hashedExprSalt :: Int
hashedExprSalt = 88172645463325252

hashText :: Text -> Int
hashText t = 
  let go t h =
        case T.uncons t of
          Just (c, t') -> go t' (xorshift h + ord c)
          Nothing -> xorshift h
  in  go t hashedExprSalt

hashedExprVar :: Text -> HashedExpr
hashedExprVar v     = HashedExprVar    (hashText v) v
hashedExprBottom :: HashedExpr
hashedExprBottom    = HashedExprBottom (xorshift (0 + hashedExprSalt))
hashedImplies :: HashedExpr -> HashedExpr -> HashedExpr
hashedImplies e1 e2 = HashedImplies    (xorshift (getHash e1 * 5 + getHash e2 * 3 + 0)) e1 e2
hashedAnd :: HashedExpr -> HashedExpr -> HashedExpr
hashedAnd     e1 e2 = HashedAnd        (xorshift (getHash e1 * 5 + getHash e2 * 3 + 1)) e1 e2
hashedOr :: HashedExpr -> HashedExpr -> HashedExpr
hashedOr      e1 e2 = HashedOr         (xorshift (getHash e1 * 5 + getHash e2 * 3 + 2)) e1 e2


{-


hashWithSalt' :: Int# -> Expr -> Int#
hashWithSalt' salt expr =
  case expr of
    ExprVar (I# t) -> xorshift (salt +# t) -- case MD5.hash ( t) of hash -> fromIntegral (BS.index hash 0) + fromIntegral (BS.index hash 1) * 256 + fromIntegral (BS.index hash 2) * 65536 + fromIntegral (BS.index hash 3) * 16777216  
    ExprBottom     -> xorshift salt
    Implies e1 e2  -> xorshift (hashWithSalt' salt e1 *# 5# +# hashWithSalt' salt e2) *# 3# +# 0#
    And     e1 e2  -> xorshift (hashWithSalt' salt e1 *# 5# +# hashWithSalt' salt e2) *# 3# +# 1#
    Or      e1 e2  -> xorshift (hashWithSalt' salt e1 *# 5# +# hashWithSalt' salt e2) *# 3# +# 2#
-}

instance Show HashedExpr where
  show e = unpack (showTypeText e)

showTypeText :: HashedExpr -> Text
showTypeText (HashedExprBottom _) = "⊥"
showTypeText (HashedExprVar _ tv) = tv

showTypeText (HashedImplies _ (HashedExprVar h1 v1) (HashedExprVar h2 v2))    =        showTypeText (HashedExprVar h1 v1) <>  " → "  <> showTypeText (HashedExprVar h2 v2)
showTypeText (HashedImplies _                t1     (HashedExprVar h2 v2))    = "(" <> showTypeText                   t1  <> ") → "  <> showTypeText (HashedExprVar h2 v2)
showTypeText (HashedImplies _ (HashedExprVar h1 v1) (HashedImplies h2 t2 t3)) =        showTypeText (HashedExprVar h1 v1) <>  " → "  <> showTypeText (HashedImplies h2 t2 t3)
showTypeText (HashedImplies _ (HashedExprVar h1 v1)                   t2 )    =        showTypeText (HashedExprVar h1 v1) <>  " → (" <> showTypeText                t2     <> ")"
showTypeText (HashedImplies _                t1                       t2 )    = "(" <> showTypeText                   t1  <> ") → (" <> showTypeText                t2     <> ")"

showTypeText (HashedAnd _ (HashedExprVar h1 v1) (HashedExprVar h2 v2))    =        showTypeText (HashedExprVar h1 v1) <>  " ∧ "  <> showTypeText (HashedExprVar h2 v2)
showTypeText (HashedAnd _ (HashedAnd h1 t1 t3)  (HashedExprVar h2 v2))    =        showTypeText (HashedAnd h1 t1 t3)  <>  " ∧ "  <> showTypeText (HashedExprVar h2 v2)
showTypeText (HashedAnd _                  t1   (HashedExprVar h2 v2))    = "(" <> showTypeText               t1      <> ") ∧ "  <> showTypeText (HashedExprVar h2 v2)
showTypeText (HashedAnd _ (HashedExprVar h1 v1) (HashedAnd h2 t2 t3) )    =        showTypeText (HashedExprVar h1 v1) <>  " ∧ "  <> showTypeText (HashedAnd h2 t2 t3)
showTypeText (HashedAnd _ (HashedExprVar h1 v1)               t2     )    =        showTypeText (HashedExprVar h1 v1) <>  " ∧ (" <> showTypeText               t2     <> ")"
showTypeText (HashedAnd _ (HashedAnd h1 t1 t2)  (HashedAnd h2 t3 t4) )    =        showTypeText (HashedAnd h1 t1 t2)  <>  " ∧ "  <> showTypeText (HashedAnd h2 t3 t4)
showTypeText (HashedAnd _                t1                 t2 )          = "(" <> showTypeText               t1      <> ") ∧ (" <> showTypeText               t2     <> ")"

showTypeText (HashedOr _ (HashedExprVar h1 v1) (HashedExprVar h2 v2))    =        showTypeText (HashedExprVar h1 v1) <>  " ∨ "  <> showTypeText (HashedExprVar h2 v2)
showTypeText (HashedOr _ (HashedOr h1  t1 t3)  (HashedExprVar h2 v2))    =        showTypeText (HashedOr h1  t1 t3)  <>  " ∨ "  <> showTypeText (HashedExprVar h2 v2)
showTypeText (HashedOr _                t1     (HashedExprVar h2 v2))    = "(" <> showTypeText               t1      <> ") ∨ "  <> showTypeText (HashedExprVar h2 v2)
showTypeText (HashedOr _ (HashedExprVar h1 v1) (HashedOr h2  t2 t3) )    =        showTypeText (HashedExprVar h1 v1) <>  " ∨ "  <> showTypeText (HashedOr h2  t2 t3)
showTypeText (HashedOr _ (HashedExprVar h1 v1)                t2    )    =        showTypeText (HashedExprVar h1 v1) <>  " ∨ (" <> showTypeText               t2     <> ")"
showTypeText (HashedOr _ (HashedOr h1  t1 t2 ) (HashedOr h2  t3 t4) )    =        showTypeText (HashedOr h1  t1 t2)  <>  " ∨ "  <> showTypeText (HashedOr h2  t3 t4)
showTypeText (HashedOr _               t1                    t2     )    = "(" <> showTypeText           t1          <> ") ∨ (" <> showTypeText               t2     <> ")"



typeVarToText :: TypeVar -> Text
typeVarToText (TypeVar x) = x
typeVarToText Bottom = "⊥"


showExprWithPars :: HashedExpr -> String
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

{-
textExprtoHashedExpr :: TextExpr -> (HashedExpr, M.Map Int Text)
textExprtoHashedExpr expr =
  let textExprtoHashedExpr' :: TextExpr -> Int -> M.Map Text Int -> M.Map Int Text -> (HashedExpr, Int, M.Map Text Int, M.Map Int Text)
      textExprtoHashedExpr' t i m revm =
        case t of
          TextExprBottom -> (hashedExprBottom, i, m, revm)

          TextExprVar tv ->
            case M.lookup tv m of
              Nothing -> (hashedExprVar (i+1), i+1, M.insert tv (i+1) m, M.insert (i+1) tv revm)
              Just j  -> (hashedExprVar j, i,  m, revm)

          TextAnd t1 t2 ->
            let (e1, i' , m' , revm' ) = textExprtoHashedExpr' t1 i  m  revm
                (e2, i'', m'', revm'') = textExprtoHashedExpr' t2 i' m' revm'
            in  (hashedAnd e1 e2, i'', m'', revm'')

          TextOr t1 t2 ->
            let (e1, i' , m' , revm' ) = textExprtoHashedExpr' t1 i  m  revm
                (e2, i'', m'', revm'') = textExprtoHashedExpr' t2 i' m' revm'
            in  (hashedOr e1 e2, i'', m'', revm'')

          TextImplies t1 t2 ->
            let (e1, i' , m' , revm' ) = textExprtoHashedExpr' t1 i  m  revm
                (e2, i'', m'', revm'') = textExprtoHashedExpr' t2 i' m' revm'
            in  (hashedImplies e1 e2, i'', m'', revm'')
  in case textExprtoHashedExpr' expr 1 M.empty M.empty of (expr', _, _, revm) -> (expr', revm)

hashedExprToTextExpr :: M.Map Int Text -> HashedExpr -> TextExpr
hashedExprToTextExpr revm expr =
  case expr of
    HashedExprBottom _     -> TextExprBottom
    HashedExprVar _ i      -> TextExprVar $ fromMaybe "ERROR!" (M.lookup i revm)
    HashedAnd _     e1 e2  -> TextAnd (hashedExprToTextExpr revm e1) (hashedExprToTextExpr revm e2)
    HashedOr  _     e1 e2  -> TextOr  (hashedExprToTextExpr revm e1) (hashedExprToTextExpr revm e2)
    HashedImplies _ e1 e2  -> TextAnd (hashedExprToTextExpr revm e1) (hashedExprToTextExpr revm e2)
-}
