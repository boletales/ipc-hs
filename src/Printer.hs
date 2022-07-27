{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Printer(
    getType,
    showWithType,
    showWithIndent,
    toProofTree,
    toProofTree2,
    toProofTree_cm_ayf
) where

import Types
import Data.Text as T
import GHC.Stack
import qualified Data.List as L
import Data.Map as M

showExprWithPars t =
  case t of
    ExprVar _ -> show t
    _         -> "(" <> show t <> ")"

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
getType (BuiltInAbsurd t1      ) = Right $ ExprBottom `Implies` t1


showWithType :: Proof -> [Char]
showWithType proof = "(" <> show proof <> ")::" <> either id show (getType proof)

tshow :: Show a => a -> Text
tshow = pack . show

showWithIndent :: Proof -> [Char]
showWithIndent proof =
  let go level p =
        let indent = L.replicate (level*2) ' '
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
  in escapeLaTeX $ intercalate "\n" $ ["\\begin{prooftree}"] <> go (fst $ changeVarName prf 1 M.empty) <> ["\\end{prooftree}"]



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
  in intercalate "\n" $ go (fst $ changeVarName prf 1 M.empty)

changeVarName :: Proof -> Int -> Map Text Text -> (Proof, Int)
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

showTypeText  ExprBottom  = "⊥"
showTypeText (ExprVar tv) = tv

showTypeText (Implies (ExprVar v1) (ExprVar v2))    =        showTypeText (ExprVar v1) <>  " → "  <> showTypeText (ExprVar v2)
showTypeText (Implies          t1  (ExprVar v2))    = "(" <> showTypeText          t1  <> ") → "  <> showTypeText (ExprVar v2)
showTypeText (Implies (ExprVar v1) (Implies t2 t3)) =        showTypeText (ExprVar v1) <>  " → "  <> showTypeText (Implies t2 t3)
showTypeText (Implies (ExprVar v1)          t2 )    =        showTypeText (ExprVar v1) <>  " → (" <> showTypeText          t2     <> ")"
showTypeText (Implies          t1           t2 )    = "(" <> showTypeText          t1  <> ") → (" <> showTypeText          t2     <> ")"

showTypeText (And (ExprVar v1) (ExprVar v2))    =        showTypeText (ExprVar v1) <>  " ∧ "  <> showTypeText (ExprVar v2)
showTypeText (And (And t1 t3)  (ExprVar v2))    =        showTypeText (And t1 t3)  <>  " ∧ "  <> showTypeText (ExprVar v2)
showTypeText (And          t1  (ExprVar v2))    = "(" <> showTypeText          t1  <> ") ∧ "  <> showTypeText (ExprVar v2)
showTypeText (And (ExprVar v1) (And t2 t3) )    =        showTypeText (ExprVar v1) <>  " ∧ "  <> showTypeText (And t2 t3)
showTypeText (And (ExprVar v1)          t2 )    =        showTypeText (ExprVar v1) <>  " ∧ (" <> showTypeText          t2     <> ")"
showTypeText (And (And t1 t2)  (And t3 t4) )    =        showTypeText (And t1 t2)  <>  " ∧ "  <> showTypeText (And t3 t4)
showTypeText (And          t1           t2 )    = "(" <> showTypeText          t1  <> ") ∧ (" <> showTypeText          t2     <> ")"

showTypeText (Or  (ExprVar v1) (ExprVar v2))    =        showTypeText (ExprVar v1) <>  " ∨ "  <> showTypeText (ExprVar v2)
showTypeText (Or  (Or  t1 t3)  (ExprVar v2))    =        showTypeText (Or  t1 t3)  <>  " ∨ "  <> showTypeText (ExprVar v2)
showTypeText (Or           t1  (ExprVar v2))    = "(" <> showTypeText          t1  <> ") ∨ "  <> showTypeText (ExprVar v2)
showTypeText (Or  (ExprVar v1) (Or  t2 t3) )    =        showTypeText (ExprVar v1) <>  " ∨ "  <> showTypeText (Or  t2 t3)
showTypeText (Or  (ExprVar v1)          t2 )    =        showTypeText (ExprVar v1) <>  " ∨ (" <> showTypeText          t2     <> ")"
showTypeText (Or  (Or  t1 t2)  (Or  t3 t4) )    =        showTypeText (Or  t1 t2)  <>  " ∨ "  <> showTypeText (Or  t3 t4)
showTypeText (Or           t1           t2 )    = "(" <> showTypeText          t1  <> ") ∨ (" <> showTypeText          t2     <> ")"

toProofTree_cm_ayf :: Proof -> Text
toProofTree_cm_ayf prf =
  let typeText p = either pack showTypeText (getType p)
      go indents' indents p =
        indents' <> "+ " <> go1 indents' indents p

      go1 indents' indents p =
        case p of
          ProofVar (LambdaVar n t)    -> showTypeText t <> " from: " <> n <> "\n"
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