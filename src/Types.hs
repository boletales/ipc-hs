{-# LANGUAGE OverloadedStrings #-}

module Types (
    TypeVar(..),
    Expr(..),
    LambdaVar(..),
    Proof(..),
    getType,
    showWithType,
    showWithIndent,
    toProofTree,
    toProofTree2,
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

getType :: Proof -> Either [Char] Expr
getType (ProofVar (LambdaVar n t))   = Right t
getType (ProofAbs (LambdaVar n t) p) = Implies t <$> getType p
getType (ProofApp p1 p2) =
  case getType p1 of
    Left e -> Left e
    Right (Implies t2 t1')
      | Right t2 == getType p2 -> Right t1'
    _ -> Left $ "cannot apply " <> show (getType p2) <> " to " <> show (getType p1) <> "!"

getType (BuiltInTuple  t1 t2   ) = Right $ t1 `Implies` (t2 `Implies` (t1 `And` t2))
getType (BuiltInFst    t1 t2   ) = Right $ (t1 `And` t2) `Implies` t1
getType (BuiltInSnd    t1 t2   ) = Right $ (t1 `And` t2) `Implies` t2
getType (BuiltInEither t1 t2 t3) = Right $ (t1 `Or` t2) `Implies` ((t1 `Implies` t3) `Implies` ((t2 `Implies` t3) `Implies` t3))
getType (BuiltInLeft   t1 t2   ) = Right $ t1 `Implies` (t1 `Or` t2)
getType (BuiltInRight  t1 t2   ) = Right $ t2 `Implies` (t1 `Or` t2)
getType (BuiltInAbsurd t1      ) = Right $ ExprVar Bottom `Implies` t1


showWithType :: Proof -> [Char]
showWithType proof = "(" <> show proof <> ")::" <> either id show (getType proof)

tshow :: Show a => a -> Text
tshow = pack . show

showWithIndent :: Proof -> [Char]
showWithIndent proof =
  let go level p =
        let indent = (L.replicate (level*2) ' ')
        in case p of
            ProofAbs (LambdaVar n t) p'  -> indent <> "(\\" <> unpack n <> "::" <> showExprWithPars t <> " -> \n"
                                                   <> go (level + 1) p' <> "\n" <>
                                            indent <> ")"
            ProofApp (ProofApp p1 p2) p3 -> indent <> "(\n" <>
                                              go (level+1) p1 <> "\n" <>
                                              go (level+1) p2 <> "\n" <>
                                              go (level+1) p3 <> "\n" <>
                                            indent <> ")"

            ProofApp p1 p2               -> indent <> "(\n" <>
                                              go (level+1) p1 <> "\n" <>
                                              go (level+1) p2 <> "\n" <>
                                            indent <> ")"
            _                            -> indent <> show p
  in go 0 proof 

escapeLaTeX =
    replace "⊥" "\\bot "
  . replace "→" "\\to "
  . replace "∧" "\\land "
  . replace "∨" "\\lor "
  . replace "￢" "\\lnot "

toProofTree :: Proof -> Text
toProofTree prf =
  let typeText p = either (const "ERROR!") tshow (getType p)
      go p =
        case p of
          ProofVar (LambdaVar n t)    -> ["\\AxiomC{$["<> tshow t <>"]_{" <> n <> "}$}"]
          ProofAbs (LambdaVar n _) pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, "<> n <>"}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]

          ProofApp (ProofApp (BuiltInTuple ex ex') pr) pr' -> go pr <> go pr' <> ["\\RightLabel{${\\scriptsize \\, (∧\\mathrm{I})}$}", "\\BinaryInfC{$" <> typeText p <> "$}"]
          ProofApp (BuiltInFst ex ex') pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, (∧\\mathrm{E}_1)}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]
          ProofApp (BuiltInSnd ex ex') pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, (∧\\mathrm{E}_2)}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]
          ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') pr ) pr') pr'' -> go pr <> go pr' <> go pr'' <> ["\\RightLabel{${\\scriptsize \\, (∨\\mathrm{E})}$}", "\\TrinaryInfC{$" <> typeText p <> "$}"]
          ProofApp (BuiltInLeft  ex ex') pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, (∨\\mathrm{I}_1)}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]
          ProofApp (BuiltInRight ex ex') pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, (∨\\mathrm{I}_2)}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]
          ProofApp (BuiltInAbsurd ex) pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, (⊥\\mathrm{E})}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]

          ProofApp pr pr'             -> go pr <> go pr' <> ["\\BinaryInfC{$" <> typeText p <> "$}"]

          BuiltInTuple  ex ex'        -> go (ProofAbs (LambdaVar "α" ex) (ProofAbs (LambdaVar "β" ex') (ProofApp (ProofApp (BuiltInTuple ex ex') (ProofVar (LambdaVar "α" ex))) (ProofVar (LambdaVar "β" ex')))))
          BuiltInFst    ex ex'        -> go (ProofAbs (LambdaVar "α" ex ) (ProofApp (BuiltInFst ex ex') (ProofVar (LambdaVar "α" ex))))
          BuiltInSnd    ex ex'        -> go (ProofAbs (LambdaVar "α" ex') (ProofApp (BuiltInSnd ex ex') (ProofVar (LambdaVar "α" ex'))))
          BuiltInEither ex ex' ex''   -> go (ProofAbs (LambdaVar "α" ex) (ProofAbs (LambdaVar "β" ex') (ProofAbs (LambdaVar "γ" ex'') (ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') (ProofVar (LambdaVar "α" ex))) (ProofVar (LambdaVar "β" ex'))) (ProofVar (LambdaVar "γ" ex''))))))
          BuiltInLeft   ex ex'        -> go (ProofAbs (LambdaVar "α" ex ) (ProofApp (BuiltInLeft ex ex') (ProofVar (LambdaVar "α" ex))))
          BuiltInRight  ex ex'        -> go (ProofAbs (LambdaVar "α" ex') (ProofApp (BuiltInRight ex ex') (ProofVar (LambdaVar "α" ex'))))
          BuiltInAbsurd ex            -> go (ProofAbs (LambdaVar "α" ex) (ProofApp (BuiltInAbsurd ex) (ProofVar (LambdaVar "α" ex))))
  in escapeLaTeX $ intercalate "\n" $ ["\\begin{prooftree}"] <> go prf <> ["\\end{prooftree}"]



toProofTree2 :: Proof -> Text
toProofTree2 prf =
  let typeText p = either (const "ERROR!") tshow (getType p)
      go p =
        case p of
          ProofVar (LambdaVar n t)    -> ["["<> tshow t <>"]_{" <> n <> "}"]
          ProofAbs (LambdaVar n _) pr ->                                                      go pr <>                                                 [typeText p <> "#" <> n]

          ProofApp (ProofApp (BuiltInTuple ex ex') pr) pr' ->                        ["{"] <> go pr <> [","] <> go pr' <>                     ["}"] <> [typeText p <> "#" <> "(∧I)"]
          ProofApp (BuiltInFst ex ex') pr ->                                         ["{"] <> go pr <>                                        ["}"] <> [typeText p <> "#" <> "(∧E_1)"]
          ProofApp (BuiltInSnd ex ex') pr ->                                         ["{"] <> go pr <>                                        ["}"] <> [typeText p <> "#" <> "(∧E_2)"]
          ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') pr ) (ProofAbs v2 pr')) (ProofAbs v3 pr'') -> ["{"] <> go pr <> [","] <> go pr' <> [","] <>  go pr'' <> ["}"] <> [typeText p <> "#" <> (if tshow v2 == tshow v3 then tshow v2 else tshow v2 <> "," <> tshow v3) <> " (∨E)"]
          ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') pr ) pr') pr'' -> ["{"] <> go pr <> [","] <> go pr' <> [","] <> go pr'' <> ["}"] <> [typeText p <> "#" <> "(∨E)"]
          ProofApp (BuiltInLeft  ex ex') pr ->                                                go pr <>                                                 [typeText p <> "#" <> "(∨I_1)"]
          ProofApp (BuiltInRight ex ex') pr ->                                                go pr <>                                                 [typeText p <> "#" <> "(∨I_1)"]
          ProofApp (BuiltInAbsurd ex) pr ->                                                   go pr <>                                                 [typeText p <> "#" <> "(⊥E)"]

          ProofApp pr pr'             -> ["{"] <> go pr <> [","] <> go pr' <> ["}"] <> [typeText p]

          BuiltInTuple  ex ex'        -> go (ProofAbs (LambdaVar "α" ex) (ProofAbs (LambdaVar "β" ex') (ProofApp (ProofApp (BuiltInTuple ex ex') (ProofVar (LambdaVar "α" ex))) (ProofVar (LambdaVar "β" ex')))))
          BuiltInFst    ex ex'        -> go (ProofAbs (LambdaVar "α" ex ) (ProofApp (BuiltInFst ex ex') (ProofVar (LambdaVar "α" ex))))
          BuiltInSnd    ex ex'        -> go (ProofAbs (LambdaVar "α" ex') (ProofApp (BuiltInSnd ex ex') (ProofVar (LambdaVar "α" ex'))))
          BuiltInEither ex ex' ex''   -> go (ProofAbs (LambdaVar "α" ex) (ProofAbs (LambdaVar "β" ex') (ProofAbs (LambdaVar "γ" ex'') (ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') (ProofVar (LambdaVar "α" ex))) (ProofVar (LambdaVar "β" ex'))) (ProofVar (LambdaVar "γ" ex''))))))
          BuiltInLeft   ex ex'        -> go (ProofAbs (LambdaVar "α" ex ) (ProofApp (BuiltInLeft ex ex') (ProofVar (LambdaVar "α" ex))))
          BuiltInRight  ex ex'        -> go (ProofAbs (LambdaVar "α" ex') (ProofApp (BuiltInRight ex ex') (ProofVar (LambdaVar "α" ex'))))
          BuiltInAbsurd ex            -> go (ProofAbs (LambdaVar "α" ex) (ProofApp (BuiltInAbsurd ex) (ProofVar (LambdaVar "α" ex))))
  in intercalate "\n" $ go prf