module Reduceq.Pretty
  ( displayDoc
  , displayCompact
  , pprintExpr
  ) where

import Reduceq.Prelude

import Data.Text.Prettyprint.Doc hiding ((<>))
import Data.Text.Prettyprint.Doc.Render.Text

import Reduceq.CoqAST

pprintTy :: Ty -> Doc
pprintTy TyInt = "Int"
pprintTy TyBool = "Bool"
pprintTy TyUnit = "()"
pprintTy (TyProd x y) = pprintTy x <+> "*" <+> pprintTy y

pprintOp :: IntBinop -> Doc
pprintOp IAdd = "+"
pprintOp IMul = "*"
pprintOp ISub = "-"

pprintComp :: IntComp -> Doc
pprintComp IEq = "="
pprintComp ILt = "<"
pprintComp IGt = ">"

pprintExpr :: Expr -> Doc
pprintExpr (Var (VarId id)) = pretty @Text ("v" <> show id)
pprintExpr (IntLit i)
  | i >= 0 = pretty i
  | otherwise = parens (pretty i)
pprintExpr (App f x) = (parens . align . sep) [pprintExpr f, pprintExpr x]
pprintExpr (Abs ty body) =
  (parens . hang 2 . sep) ["fun _ :" <+> pprintTy ty <> ".", pprintExpr body]
pprintExpr (Fst x) = parens ("fst" <+> pprintExpr x)
pprintExpr (Snd x) = parens ("snd" <+> pprintExpr x)
pprintExpr (Pair x y) = parens (pprintExpr x <> "," <+> pprintExpr y)
pprintExpr (If cond ifTrue ifFalse) =
  (parens . hang 3 . sep) ["if" <+> pprintExpr cond, pprintExpr ifTrue, pprintExpr ifFalse]
pprintExpr (IntBinop op x y) =
  parens (pprintExpr x <+> pprintOp op <+> pprintExpr y)
pprintExpr (IntComp comp x y) =
  parens (pprintExpr x <+> pprintComp comp <+> pprintExpr y)
pprintExpr (Iter f x) =
  parens ("iter" <+> pprintExpr f <+> pprintExpr x)
pprintExpr (Inl x) = parens ("inl" <+> pprintExpr x)
pprintExpr (Inr x) = parens ("inr" <+> pprintExpr x)
pprintExpr Unit = "()"

displayDoc :: Doc -> Text
displayDoc = renderStrict . layoutPretty defaultLayoutOptions

displayCompact :: Doc -> Text
displayCompact =
  renderStrict .
  layoutPretty (defaultLayoutOptions {layoutPageWidth = Unbounded})
