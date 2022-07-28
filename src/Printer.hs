{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Printer(
    getType,
    showWithType,
    showWithIndent,
    showTypeText,
    toProofTree,
    toProofTree2,
    toProofTree_cm_ayf
) where

import Types
import Data.Text as T
import GHC.Stack
import qualified Data.List as L
import Data.Map as M
import Control.Category
import Prelude hiding (id, (.))

showExprWithParsText :: TextExpr -> Text
showExprWithParsText t =
  case t of
    TextExprVar _ -> showTypeText t
    _         -> "(" <> showTypeText t <> ")"

getType :: Proof -> Either [Char] HashedExpr
getType (ProofVar (LambdaVar n t))   = Right t
getType (ProofAbs (LambdaVar n t) p) = hashedImplies t <$> getType p
getType (ProofApp p1 p2) =
  case getType p1 of
    Left e -> Left e
    Right (HashedImplies _ t2 t1')
      | Right t2 == getType p2 -> Right t1'
    _ -> Left $ "cannot apply " <> show (getType p2) <> " to " <> show (getType p1) <> "!"

getType (BuiltInTuple  t1 t2   ) = Right $ t1 `hashedImplies` (t2 `hashedImplies` (t1 `hashedAnd` t2))
getType (BuiltInFst    t1 t2   ) = Right $ (t1 `hashedAnd` t2) `hashedImplies` t1
getType (BuiltInSnd    t1 t2   ) = Right $ (t1 `hashedAnd` t2) `hashedImplies` t2
getType (BuiltInEither t1 t2 t3) = Right $ (t1 `hashedOr` t2) `hashedImplies` ((t1 `hashedImplies` t3) `hashedImplies` ((t2 `hashedImplies` t3) `hashedImplies` t3))
getType (BuiltInLeft   t1 t2   ) = Right $ t1 `hashedImplies` (t1 `hashedOr` t2)
getType (BuiltInRight  t1 t2   ) = Right $ t2 `hashedImplies` (t1 `hashedOr` t2)
getType (BuiltInAbsurd t1      ) = Right $ hashedExprBottom `hashedImplies` t1


showWithType :: Proof -> [Char]
showWithType proof = "(" <> show proof <> ")::" <> either id show (getType proof)

tshow :: Show a => a -> Text
tshow = pack . show

showWithIndent :: M.Map Int Text -> Proof -> Text
showWithIndent revmap proof =
  let go level p =
        let indent = T.replicate (level*2) " "
        in case p of
            ProofAbs (LambdaVar n t) p'  -> indent <> "(\\" <> n <> "::" <> showExprWithParsText (hashedExprToTextExpr revmap t) <> " -> \n"
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
            _                            -> indent <> tshow p
  in go 0 proof

escapeLaTeX =
    replace "⊥" "\\bot "
  . replace "→" "\\to "
  . replace "∧" "\\land "
  . replace "∨" "\\lor "
  . replace "￢" "\\lnot "

toProofTree :: M.Map Int Text -> Proof -> Text
toProofTree revmap prf =
  let typeText p = either (const "ERROR!") (hashedExprToTextExpr revmap >>> showTypeText) (getType p)
      go p =
        case p of
          ProofVar (LambdaVar n t)    -> ["\\AxiomC{$["<> (hashedExprToTextExpr revmap >>> showTypeText) t <>"]_{" <> n <> "}$}"]
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
  in escapeLaTeX $ intercalate "\n" $ ["\\begin{prooftree}"] <> go (fst $ changeVarName prf 1 M.empty) <> ["\\end{prooftree}"]



toProofTree2 :: M.Map Int Text -> Proof -> Text
toProofTree2 revmap prf =
  let typeText p = either (const "ERROR!") (hashedExprToTextExpr revmap >>> showTypeText) (getType p)
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
  in intercalate "\n" $ go (fst $ changeVarName prf 1 M.empty)

changeVarName :: Proof -> Int -> M.Map Text Text -> (Proof, Int)
changeVarName p i m =
  case p of
    ProofAbs (LambdaVar n t) p ->
      let (result, i') = changeVarName p (i+1) (M.insert n (tshow i) m)
      in  (ProofAbs (LambdaVar (tshow i) t) result, i')
    ProofApp p1 p2 ->
      let (r1, i' ) = changeVarName p1 i  m
          (r2, i'') = changeVarName p2 i' m
      in (ProofApp r1 r2, i'')
    ProofVar (LambdaVar n t) ->
      case M.lookup n m of
        Nothing -> (p, i)
        Just n' -> (ProofVar (LambdaVar n' t), i)
    _ -> (p, i)





typeVarToText (TypeVar x) = x
typeVarToText Bottom = "⊥"

showTypeText  TextExprBottom  = "⊥"
showTypeText (TextExprVar tv) = tshow tv

showTypeText (TextImplies (TextExprVar v1) (TextExprVar v2))    =        showTypeText (TextExprVar v1) <>  " → "  <> showTypeText (TextExprVar v2)
showTypeText (TextImplies          t1      (TextExprVar v2))    = "(" <> showTypeText          t1      <> ") → "  <> showTypeText (TextExprVar v2)
showTypeText (TextImplies (TextExprVar v1) (TextImplies t2 t3)) =        showTypeText (TextExprVar v1) <>  " → "  <> showTypeText (TextImplies t2 t3)
showTypeText (TextImplies (TextExprVar v1)              t2 )    =        showTypeText (TextExprVar v1) <>  " → (" <> showTypeText          t2     <> ")"
showTypeText (TextImplies          t1                   t2 )    = "(" <> showTypeText              t1  <> ") → (" <> showTypeText          t2     <> ")"

showTypeText (TextAnd (TextExprVar v1) (TextExprVar v2))    =        showTypeText (TextExprVar v1) <>  " ∧ "  <> showTypeText (TextExprVar v2)
showTypeText (TextAnd (TextAnd t1 t3)  (TextExprVar v2))    =        showTypeText (TextAnd t1 t3)  <>  " ∧ "  <> showTypeText (TextExprVar v2)
showTypeText (TextAnd          t1      (TextExprVar v2))    = "(" <> showTypeText              t1  <> ") ∧ "  <> showTypeText (TextExprVar v2)
showTypeText (TextAnd (TextExprVar v1) (TextAnd t2 t3) )    =        showTypeText (TextExprVar v1) <>  " ∧ "  <> showTypeText (TextAnd t2 t3)
showTypeText (TextAnd (TextExprVar v1)              t2 )    =        showTypeText (TextExprVar v1) <>  " ∧ (" <> showTypeText          t2     <> ")"
showTypeText (TextAnd (TextAnd t1 t2)  (TextAnd t3 t4) )    =        showTypeText (TextAnd t1 t2)  <>  " ∧ "  <> showTypeText (TextAnd t3 t4)
showTypeText (TextAnd          t1                   t2 )    = "(" <> showTypeText              t1  <> ") ∧ (" <> showTypeText          t2     <> ")"

showTypeText (TextOr  (TextExprVar v1) (TextExprVar v2))    =        showTypeText (TextExprVar v1) <>  " ∨ "  <> showTypeText (TextExprVar v2)
showTypeText (TextOr  (TextOr  t1 t3)  (TextExprVar v2))    =        showTypeText (TextOr  t1 t3)  <>  " ∨ "  <> showTypeText (TextExprVar v2)
showTypeText (TextOr           t1      (TextExprVar v2))    = "(" <> showTypeText              t1  <> ") ∨ "  <> showTypeText (TextExprVar v2)
showTypeText (TextOr  (TextExprVar v1) (TextOr  t2 t3) )    =        showTypeText (TextExprVar v1) <>  " ∨ "  <> showTypeText (TextOr  t2 t3)
showTypeText (TextOr  (TextExprVar v1)              t2 )    =        showTypeText (TextExprVar v1) <>  " ∨ (" <> showTypeText          t2     <> ")"
showTypeText (TextOr  (TextOr  t1 t2)  (TextOr  t3 t4) )    =        showTypeText (TextOr  t1 t2)  <>  " ∨ "  <> showTypeText (TextOr  t3 t4)
showTypeText (TextOr           t1                   t2 )    = "(" <> showTypeText              t1  <> ") ∨ (" <> showTypeText          t2     <> ")"

toProofTree_cm_ayf :: M.Map Int Text -> Proof -> Text
toProofTree_cm_ayf revmap prf =
  let typeText p = either pack (hashedExprToTextExpr revmap >>> showTypeText) (getType p)
      go indents' indents p =
        indents' <> "+ " <> go1 indents' indents p

      go1 indents' indents p =
        case p of
          ProofVar (LambdaVar n t)    -> showTypeText (hashedExprToTextExpr revmap t) <> " from: " <> n <> "\n"
          ProofAbs (LambdaVar n _) pr -> typeText p <> "\n" <> go indents (indents<>"  ") pr

          ProofApp (ProofApp (BuiltInTuple ex ex') pr) pr' -> typeText p <> "\n" <> go indents (indents<>"| ") pr <> go indents (indents<>"  ") pr'
          ProofApp (BuiltInFst ex ex') pr ->                  typeText p <> "\n" <> go indents (indents<>"  ") pr
          ProofApp (BuiltInSnd ex ex') pr ->                  typeText p <> "\n" <> go indents (indents<>"  ") pr
          ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') pr ) (ProofAbs v2 pr')) (ProofAbs v3 pr'') -> typeText p <> "\n" <> go indents (indents<>"| ") pr <> go indents (indents<>"| ") pr' <> go indents (indents<>"  ") pr''
          ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') pr ) pr') pr'' ->                             typeText p <> "\n" <> go indents (indents<>"| ") pr <> go indents (indents<>"| ") pr' <> go indents (indents<>"  ") pr''
          ProofApp (BuiltInLeft  ex ex') pr -> typeText p <> "\n" <> go indents (indents<>"  ") pr
          ProofApp (BuiltInRight ex ex') pr -> typeText p <> "\n" <> go indents (indents<>"  ") pr
          ProofApp (BuiltInAbsurd ex) pr ->    typeText p <> "\n" <> go indents (indents<>"  ") pr

          ProofApp pr pr'             -> typeText p <> "\n" <> go indents (indents<>"| ") pr <> go indents(indents<>"  ") pr'

          BuiltInTuple  ex ex'        -> go indents' indents (ProofAbs (LambdaVar "α" ex) (ProofAbs (LambdaVar "β" ex') (ProofApp (ProofApp (BuiltInTuple ex ex') (ProofVar (LambdaVar "α" ex))) (ProofVar (LambdaVar "β" ex')))))
          BuiltInFst    ex ex'        -> go indents' indents (ProofAbs (LambdaVar "α" ex ) (ProofApp (BuiltInFst ex ex') (ProofVar (LambdaVar "α" ex))))
          BuiltInSnd    ex ex'        -> go indents' indents (ProofAbs (LambdaVar "α" ex') (ProofApp (BuiltInSnd ex ex') (ProofVar (LambdaVar "α" ex'))))
          BuiltInEither ex ex' ex''   -> go indents' indents (ProofAbs (LambdaVar "α" ex) (ProofAbs (LambdaVar "β" ex') (ProofAbs (LambdaVar "γ" ex'') (ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') (ProofVar (LambdaVar "α" ex))) (ProofVar (LambdaVar "β" ex'))) (ProofVar (LambdaVar "γ" ex''))))))
          BuiltInLeft   ex ex'        -> go indents' indents (ProofAbs (LambdaVar "α" ex ) (ProofApp (BuiltInLeft ex ex') (ProofVar (LambdaVar "α" ex))))
          BuiltInRight  ex ex'        -> go indents' indents (ProofAbs (LambdaVar "α" ex') (ProofApp (BuiltInRight ex ex') (ProofVar (LambdaVar "α" ex'))))
          BuiltInAbsurd ex            -> go indents' indents (ProofAbs (LambdaVar "α" ex) (ProofApp (BuiltInAbsurd ex) (ProofVar (LambdaVar "α" ex))))
  in go1 "" "" (fst $ changeVarName prf 1 M.empty)