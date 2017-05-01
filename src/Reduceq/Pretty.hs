module Reduceq.Pretty
  ( displayDoc
  , pprintExpr
  ) where

import           Reduceq.Prelude

import qualified Data.Text as Text
import           Text.PrettyPrint.Leijen.Text

import           Reduceq.CoqAST

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
pprintExpr (Var (VarId id)) = text ("v" <> show id)
pprintExpr (IntLit i)
  | i >= 0 = integer i
  | i < 0 = parens (integer i)
pprintExpr (App f x) = parens (pprintExpr f <+> pprintExpr x)
pprintExpr (Abs ty body) = parens ("fun _ :" <+> pprintTy ty <> "." <+> pprintExpr body)
pprintExpr (Fst x) = parens ("fst" <+> pprintExpr x)
pprintExpr (Snd x) = parens ("snd" <+> pprintExpr x)
pprintExpr (Pair x y) = parens (pprintExpr x <> "," <+> pprintExpr y)
pprintExpr (If cond ifTrue ifFalse) =
  parens ("if" <+> pprintExpr cond <+> pprintExpr ifTrue <+> pprintExpr ifFalse)
pprintExpr (IntBinop op x y) =
  parens (pprintExpr x <+> pprintOp op <+> pprintExpr y)
pprintExpr (IntComp comp x y) =
  parens (pprintExpr x <+> pprintComp comp <+> pprintExpr y)

displayDoc :: Doc -> Text
displayDoc = displayTStrict . renderPretty 0.8 80
