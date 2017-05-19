module Reduceq.PrettyCoq
  ( displayDoc
  , pprintExample
  , pprintExpr
  , pprintTy
  ) where

import Reduceq.Prelude

import Data.Text.Prettyprint.Doc as Pretty
import Data.Text.Prettyprint.Doc.Render.Text

import Reduceq.CoqAST

pprintVar :: VarId -> Doc a
pprintVar (VarId index) = parens ("tvar" <+> pretty index)

pprintTy :: Ty -> Doc a
pprintTy ty =
  case ty of
    TyInt -> "TInt"
    TyReal -> "TReal"
    TyBool -> "TBool"
    TyUnit -> "TUnit"
    TyProd x y -> parens ("TProd " <+> pprintTy x <+> pprintTy y)
    TyArr t -> parens ("TList" <+> pprintTy t)
    TyFun cod dom -> parens ("TArrow" <+> pprintTy cod <+> pprintTy dom)
    TySum l r -> parens ("TSum" <+> pprintTy l <+> pprintTy r)

pprintOp :: IntBinop -> Doc a
pprintOp op =
  case op of
    IAdd -> "Add"
    IMul -> "Mul"
    ISub -> "Sub"

pprintComp :: IntComp -> Doc a
pprintComp comp =
  case comp of
    IEq -> "Eq"
    ILt -> "Lt"
    IGt -> "Gt"

pprintExpr :: Expr VarId -> Doc a
pprintExpr (Var id) = pprintVar id
pprintExpr (IntLit i) =
  let lit
        | i >= 0 = pretty i
        | otherwise = parens (pretty i)
  in parens ("tint" <+> lit)
pprintExpr (App f x) = (parens . align) (pprintExpr f <+> pprintExpr x)
pprintExpr (Abs ty body) = parens ("tabs" <+> pprintTy ty <+> pprintExpr body)
pprintExpr (Fst x) = parens ("tfst" <+> pprintExpr x)
pprintExpr (Snd x) = parens ("tsnd" <+> pprintExpr x)
pprintExpr (Pair x y) =
  parens
    ("tpair" <+> pprintExpr x <+> pprintExpr y)
pprintExpr (If cond ifTrue ifFalse) =
  (parens . hang 3 . Pretty.group)
    ("tif" <+> pprintExpr cond <+> pprintExpr ifTrue <+> pprintExpr ifFalse)
pprintExpr (IntBinop op x y) =
  parens ("tint_binop" <+> pprintOp op <+> pprintExpr x <+> pprintExpr y)
pprintExpr (IntComp comp x y) =
  parens ("tint_comp" <+> pprintComp comp <+> pprintExpr x <+> pprintExpr y)
pprintExpr (Iter f x) = parens ("titer" <+> pprintExpr f <+> pprintExpr x)
pprintExpr (Inl x) =
  parens ("tinl" <+> pprintExpr x)
pprintExpr (Inr x) =
  parens ("tinr" <+> pprintExpr x)
pprintExpr (Set arr index val) =
  parens ("twrite" <+> pprintExpr arr <+> pprintExpr index <+> pprintExpr val)
pprintExpr (Read arr index) =
  parens ("tread" <+> pprintExpr arr <+> pprintExpr index)
pprintExpr Unit = "tunit"

displayDoc :: Doc a -> Text
displayDoc = renderStrict . layoutPretty defaultLayoutOptions . unAnnotate

pprintTypingLemma :: Ty -> Doc a
pprintTypingLemma ty =
  vsep
    [ "Lemma example_typing : empty_ctx |-- example \\in" <+> pprintTy ty <> "."
    , "Proof. unfold example. eauto. Qed."
    ]

pprintExample :: Expr VarId -> Ty -> Doc a
pprintExample expr ty =
  vsep
    [ "Require Import Term Typing."
    , "Definition example :=" <+> pprintExpr expr <> "."
    , pprintTypingLemma ty
    , ""
    ]