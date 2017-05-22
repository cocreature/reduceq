module Reduceq.Coq.Proof
  ( pprintExample
  , pprintProofObligation
  , PprintError(..)
  , showPprintError
  , MatchError(..)
  , strictUnion
  ) where

import           Reduceq.Prelude

import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import           Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Text.Prettyprint.Doc.Internal as PrettyInternal

import           Reduceq.Coq.AST

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
    TyArr t -> parens ("TList" <+> "Local" <+> pprintTy t)
    TyFun cod dom -> pprintApp "TArrow" [pprintTy cod, pprintTy dom]
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

pprintApp :: Doc a -> [Doc a] -> Doc a
pprintApp f xs = (parens . hang 2 . sep) (f : xs)

pprintExpr :: Expr -> Doc a
pprintExpr (Var id) = pprintVar id
pprintExpr (ExternRef (ExternReference name _)) = pretty name
pprintExpr (IntLit i) =
  let lit
        | i >= 0 = pretty i
        | otherwise = parens (pretty i)
  in parens ("tint" <+> lit)
pprintExpr (App f x) =
  pprintApp "tapp" [pprintExpr f, pprintExpr x]
pprintExpr (Abs ty body) = pprintApp "tabs" [pprintTy ty, pprintExpr body]
pprintExpr (Case x ifL ifR) =
  pprintApp "tcase" [pprintExpr x, pprintExpr ifL, pprintExpr ifR]
pprintExpr (Fst x) = parens ("tfst" <+> pprintExpr x)
pprintExpr (Snd x) = parens ("tsnd" <+> pprintExpr x)
pprintExpr (Pair x y) = pprintApp "tpair" [pprintExpr x, pprintExpr y]
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
pprintExpr (SetAtKey arr key val) =
  pprintApp "tset_at_key" [pprintExpr key, pprintExpr val, pprintExpr arr]
pprintExpr (Read arr index) =
  parens ("tread" <+> pprintExpr arr <+> pprintExpr index)
pprintExpr (ReadAtKey arr key) =
  pprintApp "tread_at_key" [pprintExpr key, pprintExpr arr]
pprintExpr Unit = "tunit"
pprintExpr (Annotated e _) = pprintExpr e
pprintExpr (Map f xs) =
  pprintApp "tmap" [pprintExpr f, pprintExpr xs]
pprintExpr (Group xs) =
  parens ("tgroup" <+> pprintExpr xs)
pprintExpr (Fold f i xs) =
  pprintApp "tfold" [pprintExpr f, pprintExpr i, pprintExpr xs]
pprintExpr (Concat xss) = parens ("tconcat" <+> pprintExpr xss)
pprintExpr (List xs) = parens ("tlist" <+> list (map pprintExpr xs))

pprintTypingJudgement :: Text -> [ExternReference] -> Ty -> Doc a
pprintTypingJudgement name externRefs ty =
  "empty_ctx |--" <+> pretty name <> refParams <+> "\\in" <+> pprintTy ty
  where
    refParams = hsep' (map (pretty . refName) externRefs)

pprintExternRefTyAssm :: ExternReference -> Doc a
pprintExternRefTyAssm (ExternReference name ty) =
  pprintTypingJudgement name [] ty <+> "->"

coqForall :: Doc a
coqForall = PrettyInternal.Text 1 "forall"

forallExtern :: [ExternReference] -> Doc a -> Doc a
forallExtern externRefs doc
  | null externRefs = doc
  | otherwise = coqForall <+> refParams <> comma <+> align doc
  where
    refParams = hsep (map (pretty . refName) externRefs)

pprintTypingLemma :: Text -> Expr -> Ty -> Doc a
pprintTypingLemma name expr ty = vsep [lemmaIntro, indent 2 body, proof]
  where
    lemmaIntro = "Lemma" <+> pretty name <> "_typing" <+> ":"
    assumptions = map pprintExternRefTyAssm externRefs
    proof =
      "Proof. unfold" <+> pretty name <> ". repeat econstructor; eauto. Qed."
    body =
      forallExtern
        externRefs
        (vsep (assumptions ++ [pprintTypingJudgement name externRefs ty <> "."]))
    externRefs = collectExternReferences expr

hsep' :: [Doc a] -> Doc a
hsep' docs
  | null docs = mempty
  | otherwise = space <> hsep docs

pprintExprDefinition :: Text -> Expr -> Doc a
pprintExprDefinition name expr =
  (hang 2 . sep)
    [ "Definition" <+> pretty name <> parameters <+> ":="
    , pprintExpr expr <> "."
    ]
  where
    externRefs = collectExternReferences expr
    parameters = hsep' (map (pretty . refName) externRefs)

pprintExample :: Expr -> Ty -> Doc a
pprintExample expr ty =
  vsep
    [ "Require Import Coq.Lists.List."
    , "Import ListNotations."
    , "Require Import Term Typing."
    , pprintExprDefinition "example" expr
    , pprintTypingLemma "example" expr ty
    , mempty
    ]

data MatchError k v =
  MatchError k
             v
             v
  deriving (Show, Eq, Ord)

data PprintError =
  DifferentExternalRefTys !(MatchError Text Ty)

showPprintError :: PprintError -> Text
showPprintError (DifferentExternalRefTys (MatchError name ty ty')) =
  "The type of the external function \"" <> name <>
  "\" is different in the two programs: " <>
  show ty <>
  "≠" <>
  show ty'

strictUnion :: (Ord k, Eq v) => Map k v -> Map k v -> Either (MatchError k v) (Map k v)
strictUnion = Map.mergeA Map.preserveMissing Map.preserveMissing whenMatched
  where
    whenMatched =
      Map.zipWithAMatched
        (\k v v' ->
           if v == v'
             then Right v
             else Left (MatchError k v v'))

pprintEquivalence :: Text -> Expr -> Expr -> Either PprintError (Doc a)
pprintEquivalence name imperative mapreduce = do
  externRefs <-
    bimap
      DifferentExternalRefTys
      (map (uncurry ExternReference) . Map.toList)
      (strictUnion imperativeRefs mapreduceRefs)
  let assumptions = map pprintExternRefTyAssm externRefs
      equivalence =
        vsep
          [ coqForall <+> "final,"
          , indent
              2
              (vsep
                 [ pprintStep "imperative" imperative "final" <+> "->"
                 , pprintStep "mapreduce" mapreduce "final" <> "."
                 ])
          ]
      body = forallExtern externRefs (vsep (assumptions ++ [equivalence]))
  Right (vsep ["Lemma" <+> pretty name <+> colon, indent 2 body, "Admitted."])
  where
    imperativeRefs = refMap imperative
    mapreduceRefs = refMap mapreduce
    pprintStep :: Text -> Expr -> Text -> Doc a
    pprintStep name' expr to' =
      "bigstep" <+>
      parens
        (pretty name' <>
         hsep' (map (pretty . refName) (collectExternReferences expr))) <+>
      pretty to'
    refMap =
      Map.fromList .
      map (\(ExternReference n t) -> (n, t)) . collectExternReferences

pprintProofObligation :: (Expr, Ty) -> (Expr, Ty) -> Either PprintError (Doc a)
pprintProofObligation (imperative, imperativeTy) (mapreduce, mapreduceTy) = do
  equivalence <- pprintEquivalence "equivalence" imperative mapreduce
  pure
    (vsep
       [ "Require Import Step Term Typing."
       , pprintExprDefinition "imperative" imperative
       , pprintExprDefinition "mapreduce" mapreduce
       , pprintTypingLemma "imperative" imperative imperativeTy
       , pprintTypingLemma "mapreduce" mapreduce mapreduceTy
       , equivalence
       , mempty
       ])
