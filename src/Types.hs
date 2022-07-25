{-# LANGUAGE OverloadedStrings #-}

module Types (
    TypeVar(..),
    Expr(..),
    LambdaVar(..),
    Proof(..)
  ) where

import Data.Text
import GHC.Stack
import qualified Data.List as L

data TypeVar =
  TypeVar Text |
  Bottom
  deriving (Eq, Ord)

instance Show TypeVar where
  show (TypeVar t) = unpack t
  show Bottom = "⊥"

data Expr =
    ExprVar TypeVar
  | Implies Expr Expr
  | And Expr Expr
  | Or Expr Expr
  deriving (Eq, Ord)

instance Show Expr where
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
