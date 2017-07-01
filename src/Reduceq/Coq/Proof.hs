module Reduceq.Coq.Proof
  ( pprintExample
  , pprintProofObligation
  , pprintProofStepsObligation
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
    TyProd x y -> parens (pprintTy x <+> ":*:" <+> pprintTy y)
    TyArr t -> parens ("TList" <+> pprintTy t)
    TyFun cod dom -> pprintApp "TArrow" [pprintTy cod, pprintTy dom]
    TySum l r -> parens ("TSum" <+> pprintTy l <+> pprintTy r)

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
pprintExpr (Abs ty body) =
  parens ("tabs" <+> (align . sep) [pprintTy ty, pprintExpr body])
pprintExpr (Case x ifL ifR) =
  pprintApp "tcase" [pprintExpr x, pprintExpr ifL, pprintExpr ifR]
pprintExpr (Fst x) = parens ("tfst" <+> pprintExpr x)
pprintExpr (Snd x) = parens ("tsnd" <+> pprintExpr x)
pprintExpr (Pair x y) = pprintApp "tpair" [pprintExpr x, pprintExpr y]
pprintExpr (If cond ifTrue ifFalse) =
  (parens . hang 3 . Pretty.group)
    ("tif" <+> pprintExpr cond <+> pprintExpr ifTrue <+> pprintExpr ifFalse)
pprintExpr (IntBinop op x y) = parens (pprintExpr x <+> op' <+> pprintExpr y)
  where
    op' =
      case op of
        IAdd -> "+"
        ISub -> "-"
        IMul -> "*"
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
  pprintApp "twrite_at_key" [pprintExpr arr, pprintExpr key, pprintExpr val]
pprintExpr (Read arr index) =
  parens ("tread" <+> pprintExpr arr <+> pprintExpr index)
pprintExpr (ReadAtKey arr key) =
  pprintApp "tread_at_key" [pprintExpr arr, pprintExpr key]
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

coqImports :: [Doc a]
coqImports =
  [ "Require Import Coq.Lists.List."
  , "Import ListNotations."
  , "Require Import" <+> localImports <> "."
  ]
  where
    localImports =
      hsep
        [ "Determinism"
        , "Misc"
        , "Notations"
        , "Preservation"
        , "Rules"
        , "Setoid_Equivalence"
        , "Step"
        , "Substitutivity"
        , "Term"
        , "Typing"
        , "Util"
        ]

pprintExample :: Expr -> Ty -> Doc a
pprintExample expr ty =
  vsep
    (coqImports ++
     [ pprintExprDefinition "example" expr
     , pprintTypingLemma "example" expr ty
     , mempty
     ])

data MatchError k v =
  MatchError k
             v
             v
  deriving (Show, Eq, Ord)

data PprintError
  = DifferentExternalRefTys !(MatchError Text Ty)
  | PprintTypeMismatch !Ty
                       !Ty

showPprintError :: PprintError -> Text
showPprintError (DifferentExternalRefTys (MatchError name ty ty')) =
  "The type of the external function \"" <> name <>
  "\" is different in the two programs: " <>
  show ty <>
  "≠" <>
  show ty'
showPprintError (PprintTypeMismatch ty ty') =
  "The programs cannot be proven equivalent because their types do not match" <>
  show ty <>
  " " <>
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

pprintEquivalentTheorem :: Text -> ProgramSteps Expr -> Ty -> Either PprintError (Doc a)
pprintEquivalentTheorem name (ProgramSteps initial steps final) ty = do
  let body =
        (hang 2 . sep)
          ((coqForall <+> hsep argNames <> ",") :
           argTyAssumptions ++
           [ pprintApp
               "equivalent"
               [ pprintApp "tapp" [pprintExpr initial, hsep argNames]
               , pprintApp "tapp" [pprintExpr final, hsep argNames]
               ] <>
             "."
           ])
  pure (vsep ["Theorem" <+> pretty name <+> colon, indent 2 body, "Admitted."])
  where
    argTyAssumptions :: [Doc a]
    argTyAssumptions =
      zipWith
        (\ty' i -> pprintTypingJudgement ("arg" <> show i) [] ty' <+> "->")
        argTys
        [1 :: Int ..]
    argTys :: [Ty]
    argTys =
      let argTys' (TyFun dom cod) = dom : argTys' cod
          argTys' _ = []
      in argTys' ty
    argNames :: [Doc a]
    argNames = map (\i -> "arg" <> pretty i) [1 .. numArgs]
    numArgs :: Int
    numArgs = length argTys

pprintEquivalence :: Text -> (Expr, Ty) -> (Expr, Ty) -> Either PprintError (Doc a)
pprintEquivalence _ (_, ty) (_, ty')
  | ty /= ty' = Left (PprintTypeMismatch ty ty')
pprintEquivalence name (imperative, ty) (mapreduce, _) = do
  externRefs <-
    bimap
      DifferentExternalRefTys
      (map (uncurry ExternReference) . Map.toList)
      (strictUnion imperativeRefs mapreduceRefs)
  let assumptions = map pprintExternRefTyAssm externRefs
      equivalence =
        (hang 2 . sep)
          ((coqForall <+> hsep argNames <+> "final,") :
           argTyAssumptions ++
           [ pprintStep "imperative" imperative "final" <+> "->"
           , pprintStep "mapreduce" mapreduce "final" <> "."
           ])
      body = forallExtern externRefs (vsep (assumptions ++ [equivalence]))
  Right (vsep ["Lemma" <+> pretty name <+> colon, indent 2 body, "Admitted."])
  where
    imperativeRefs = refMap imperative
    mapreduceRefs = refMap mapreduce
    pprintStep :: Text -> Expr -> Text -> Doc a
    pprintStep name' expr to' =
      pprintApp
        "bigstep"
        [ pprintApp
            "tapp"
            [ pprintApp
                (pretty name')
                (map (pretty . refName) (collectExternReferences expr))
            , hsep argNames
            ]
        , pretty to'
        ]
    argTyAssumptions :: [Doc a]
    argTyAssumptions =
      zipWith
        (\ty' i -> pprintTypingJudgement ("arg" <> show i) [] ty' <+> "->")
        argTys
        [1 :: Int ..]
    argTys :: [Ty]
    argTys =
      let argTys' (TyFun dom cod) = dom : argTys' cod
          argTys' _ = []
      in argTys' ty
    argNames :: [Doc a]
    argNames = map (\i -> "arg" <> pretty i) [1 .. numArgs]
    numArgs :: Int
    numArgs = length argTys
    refMap =
      Map.fromList .
      map (\(ExternReference n t) -> (n, t)) . collectExternReferences

pprintProofObligation :: (Expr, Ty) -> (Expr, Ty) -> Either PprintError (Doc a)
pprintProofObligation (imperative, imperativeTy) (mapreduce, mapreduceTy) = do
  equivalence <-
    pprintEquivalence
      "equivalence"
      (imperative, imperativeTy)
      (mapreduce, mapreduceTy)
  pure
    (vsep
       (coqImports ++
        [ pprintExprDefinition "imperative" imperative
        , pprintExprDefinition "mapreduce" mapreduce
        , pprintTypingLemma "imperative" imperative imperativeTy
        , pprintTypingLemma "mapreduce" mapreduce mapreduceTy
        , equivalence
        , mempty
        ]))

pprintProofStepsObligation :: ProgramSteps Expr -> Ty -> Either PprintError (Doc a)
pprintProofStepsObligation steps ty = do
  equivalent <- pprintEquivalentTheorem "equivalent" steps ty
  pure (vsep (coqImports ++ [equivalent]))
