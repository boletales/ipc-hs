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

showExprWithParsText :: HashedExpr -> Text
showExprWithParsText t =
  case t of
    HashedExprVar _ _ -> showTypeText t
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

showWithIndent :: Proof -> Text
showWithIndent proof =
  let go level p =
        let indent = T.replicate (level*2) " "
        in case p of
            ProofAbs (LambdaVar n t) p'  -> indent <> "(\\" <> n <> "::" <> showExprWithParsText t <> " -> \n"
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
    replace "???" "\\bot "
  . replace "???" "\\to "
  . replace "???" "\\land "
  . replace "???" "\\lor "
  . replace "???" "\\lnot "

toProofTree :: M.Map Int Text -> Proof -> Text
toProofTree revmap prf =
  let typeText p = either (const "ERROR!") showTypeText (getType p)
      go p =
        case p of
          ProofVar (LambdaVar n t)    -> ["\\AxiomC{$["<> showTypeText t <>"]_{" <> n <> "}$}"]
          ProofAbs (LambdaVar n _) pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, "<> n <>"}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]

          ProofApp (ProofApp (BuiltInTuple ex ex') pr) pr' -> go pr <> go pr' <> ["\\RightLabel{${\\scriptsize \\, (???\\mathrm{I})}$}", "\\BinaryInfC{$" <> typeText p <> "$}"]
          ProofApp (BuiltInFst ex ex') pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, (???\\mathrm{E}_1)}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]
          ProofApp (BuiltInSnd ex ex') pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, (???\\mathrm{E}_2)}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]
          ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') pr ) pr') pr'' -> go pr <> go pr' <> go pr'' <> ["\\RightLabel{${\\scriptsize \\, (???\\mathrm{E})}$}", "\\TrinaryInfC{$" <> typeText p <> "$}"]
          ProofApp (BuiltInLeft  ex ex') pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, (???\\mathrm{I}_1)}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]
          ProofApp (BuiltInRight ex ex') pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, (???\\mathrm{I}_2)}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]
          ProofApp (BuiltInAbsurd ex) pr -> go pr <> ["\\RightLabel{${\\scriptsize \\, (???\\mathrm{E})}$}", "\\UnaryInfC{$" <> typeText p <> "$}"]

          ProofApp pr pr'             -> go pr <> go pr' <> ["\\BinaryInfC{$" <> typeText p <> "$}"]

          BuiltInTuple  ex ex'        -> go (ProofAbs (LambdaVar "??" ex) (ProofAbs (LambdaVar "??" ex') (ProofApp (ProofApp (BuiltInTuple ex ex') (ProofVar (LambdaVar "??" ex))) (ProofVar (LambdaVar "??" ex')))))
          BuiltInFst    ex ex'        -> go (ProofAbs (LambdaVar "??" ex ) (ProofApp (BuiltInFst ex ex') (ProofVar (LambdaVar "??" ex))))
          BuiltInSnd    ex ex'        -> go (ProofAbs (LambdaVar "??" ex') (ProofApp (BuiltInSnd ex ex') (ProofVar (LambdaVar "??" ex'))))
          BuiltInEither ex ex' ex''   -> go (ProofAbs (LambdaVar "??" ex) (ProofAbs (LambdaVar "??" ex') (ProofAbs (LambdaVar "??" ex'') (ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') (ProofVar (LambdaVar "??" ex))) (ProofVar (LambdaVar "??" ex'))) (ProofVar (LambdaVar "??" ex''))))))
          BuiltInLeft   ex ex'        -> go (ProofAbs (LambdaVar "??" ex ) (ProofApp (BuiltInLeft ex ex') (ProofVar (LambdaVar "??" ex))))
          BuiltInRight  ex ex'        -> go (ProofAbs (LambdaVar "??" ex') (ProofApp (BuiltInRight ex ex') (ProofVar (LambdaVar "??" ex'))))
          BuiltInAbsurd ex            -> go (ProofAbs (LambdaVar "??" ex) (ProofApp (BuiltInAbsurd ex) (ProofVar (LambdaVar "??" ex))))
  in escapeLaTeX $ intercalate "\n" $ ["\\begin{prooftree}"] <> go (fst $ changeVarName prf 1 M.empty) <> ["\\end{prooftree}"]



toProofTree2 :: Proof -> Text
toProofTree2 prf =
  let typeText p = either (const "ERROR!") showTypeText (getType p)
      go :: Text -> Proof -> Text
      go str p =
        (case p of
          ProofVar (LambdaVar n t)    
            -> "[" <> showTypeText t <> "] from: " <> n <> str
          ProofAbs (LambdaVar n t) pr
            ->
              go "" pr 
              <> typeText p <> str <> " # (???I "<> n <> " :: " <> showTypeText t <> ")"

          ProofApp (ProofApp (BuiltInTuple ex ex') pr) pr' 
            ->    "{\n"
                  <> go "" pr
                  <> ",\n"
                  <> go "" pr'
               <> "}\n"
               <> typeText p <> " # (???I)"
              
          ProofApp (BuiltInFst ex ex') pr -> go "" pr
          ProofApp (BuiltInSnd ex ex') pr -> go "" pr
          ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') pr ) (ProofAbs (LambdaVar n2 t2) pr')) (ProofAbs (LambdaVar n3 t3)  pr'') 
            ->    "{\n" 
                  <> go "" pr
                  <> ",\n"
                  <> go "" pr'
                  <> ",\n"
                  <> go "" pr'
               <> "}\n"
               <> typeText p
                  <> (" # (???E. left "<>n2<>":("<> showTypeText (hashedImplies ex' ex) <> ") , right"<>n3<>":("<> showTypeText (hashedImplies ex'' ex) <>"))")
          ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') pr ) pr') pr''
            ->   "{\n" 
                  <> go "" pr
                  <> ",\n"
                  <> go "" pr'
                  <> ",\n"
                  <> go "" pr'
               <> "}\n"
               <> typeText p <> " # (???E')"
          
          ProofApp (BuiltInLeft  ex ex') pr
            ->    go "" pr
               <> typeText p <> str <> "# (???I-L)"
          
          ProofApp (BuiltInRight  ex ex') pr
            ->    go "" pr
               <> typeText p <> str <> "# (???I-R)"
          ProofApp (BuiltInAbsurd ex) pr
            ->    go "" pr
               <> typeText p <> str <> "# (???E)"

          ProofApp pr pr'             
            ->   "{\n"
                  <> go "" pr
                  <> ",\n"
                  <> go "" pr'
               <> "}\n"
               <> typeText p <> "# (???E)"


          BuiltInTuple  ex ex'        -> go "" (ProofAbs (LambdaVar "??" ex) (ProofAbs (LambdaVar "??" ex') (ProofApp (ProofApp (BuiltInTuple ex ex') (ProofVar (LambdaVar "??" ex))) (ProofVar (LambdaVar "??" ex')))))
          BuiltInFst    ex ex'        -> go "" (ProofAbs (LambdaVar "??" ex ) (ProofApp (BuiltInFst ex ex') (ProofVar (LambdaVar "??" ex))))
          BuiltInSnd    ex ex'        -> go "" (ProofAbs (LambdaVar "??" ex') (ProofApp (BuiltInSnd ex ex') (ProofVar (LambdaVar "??" ex'))))
          BuiltInEither ex ex' ex''   -> go "" (ProofAbs (LambdaVar "??" ex) (ProofAbs (LambdaVar "??" ex') (ProofAbs (LambdaVar "??" ex'') (ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') (ProofVar (LambdaVar "??" ex))) (ProofVar (LambdaVar "??" ex'))) (ProofVar (LambdaVar "??" ex''))))))
          BuiltInLeft   ex ex'        -> go "" (ProofAbs (LambdaVar "??" ex ) (ProofApp (BuiltInLeft ex ex') (ProofVar (LambdaVar "??" ex))))
          BuiltInRight  ex ex'        -> go "" (ProofAbs (LambdaVar "??" ex') (ProofApp (BuiltInRight ex ex') (ProofVar (LambdaVar "??" ex'))))
          BuiltInAbsurd ex            -> go "" (ProofAbs (LambdaVar "??" ex) (ProofApp (BuiltInAbsurd ex) (ProofVar (LambdaVar "??" ex))))
        ) <> "\n"
  in go "" (fst $ changeVarName prf 1 M.empty)

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





toProofTree_cm_ayf :: Proof -> Text
toProofTree_cm_ayf prf =
  let typeText p = either pack (showTypeText) (getType p)
      go indents' indents str p =
        indents' <> "+ " <> go1 indents' indents str p

      go1 indents' indents str p =
        case p of
          ProofVar (LambdaVar n t)    -> "[" <> showTypeText t <> "] from: " <> n <> str <> "\n"
          ProofAbs (LambdaVar n t) pr -> typeText p <> str <> " ... {"<> n <> " :: " <> showTypeText t <> "}" <> "\n" <> go indents (indents<>"  ") "" pr

          ProofApp (ProofApp (BuiltInTuple ex ex') pr) pr' -> typeText p <> str <> "\n" <> go indents (indents<>"| ") "" pr <> go indents (indents<>"  ") "" pr'
          ProofApp (BuiltInFst ex ex') pr ->                  typeText p <> str <> "\n" <> go indents (indents<>"  ") "" pr
          ProofApp (BuiltInSnd ex ex') pr ->                  typeText p <> str <> "\n" <> go indents (indents<>"  ") "" pr
          ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') pr ) (ProofAbs (LambdaVar n2 t2) pr')) (ProofAbs (LambdaVar n3 t3)  pr'')
            -> typeText p <> "\n" <> go indents (indents<>"| ") (" ... {???E. left:("<> showTypeText (hashedImplies ex' ex) <> ") , right:("<> showTypeText (hashedImplies ex'' ex) <>")}") pr <> go indents (indents<>"| ") (" ... {"<> n2 <> " (???E) :: " <> showTypeText t2 <> "}") pr' <> go indents (indents<>"  ") (" ... {"<> n3 <> " (???E) :: " <> showTypeText t3 <> "}") pr''
          ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') pr ) pr') pr'' -> typeText p <> "\n" <> go indents (indents<>"| ") "" pr <> go indents (indents<>"| ") "" pr' <> go indents (indents<>"  ") "" pr''
          ProofApp (BuiltInLeft  ex ex') pr -> typeText p <> str <> "\n" <> go indents (indents<>"  ") "" pr
          ProofApp (BuiltInRight ex ex') pr -> typeText p <> str <> "\n" <> go indents (indents<>"  ") "" pr
          ProofApp (BuiltInAbsurd ex) pr ->    typeText p <> str <> "\n" <> go indents (indents<>"  ") "" pr

          ProofApp pr pr'             -> typeText p  <> str <> "\n" <> go indents (indents<>"| ") "" pr <> go indents(indents<>"  ") "" pr'

          BuiltInTuple  ex ex'        -> go indents' indents "" (ProofAbs (LambdaVar "??" ex) (ProofAbs (LambdaVar "??" ex') (ProofApp (ProofApp (BuiltInTuple ex ex') (ProofVar (LambdaVar "??" ex))) (ProofVar (LambdaVar "??" ex')))))
          BuiltInFst    ex ex'        -> go indents' indents "" (ProofAbs (LambdaVar "??" ex ) (ProofApp (BuiltInFst ex ex') (ProofVar (LambdaVar "??" ex))))
          BuiltInSnd    ex ex'        -> go indents' indents "" (ProofAbs (LambdaVar "??" ex') (ProofApp (BuiltInSnd ex ex') (ProofVar (LambdaVar "??" ex'))))
          BuiltInEither ex ex' ex''   -> go indents' indents "" (ProofAbs (LambdaVar "??" ex) (ProofAbs (LambdaVar "??" ex') (ProofAbs (LambdaVar "??" ex'') (ProofApp (ProofApp (ProofApp (BuiltInEither ex ex' ex'') (ProofVar (LambdaVar "??" ex))) (ProofVar (LambdaVar "??" ex'))) (ProofVar (LambdaVar "??" ex''))))))
          BuiltInLeft   ex ex'        -> go indents' indents "" (ProofAbs (LambdaVar "??" ex ) (ProofApp (BuiltInLeft ex ex') (ProofVar (LambdaVar "??" ex))))
          BuiltInRight  ex ex'        -> go indents' indents "" (ProofAbs (LambdaVar "??" ex') (ProofApp (BuiltInRight ex ex') (ProofVar (LambdaVar "??" ex'))))
          BuiltInAbsurd ex            -> go indents' indents "" (ProofAbs (LambdaVar "??" ex) (ProofApp (BuiltInAbsurd ex) (ProofVar (LambdaVar "??" ex))))
  in go1 "" "" "" (fst $ changeVarName prf 1 M.empty)