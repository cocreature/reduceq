{-# LANGUAGE ViewPatterns #-}
module Reduceq.Coq.Proof
  ( pprintExample
  , pprintProofObligation
  , pprintProofStepsObligation
  , pprintDiff
  , pprintDiffs
  , PprintError(..)
  , showPprintError
  , MatchError(..)
  , strictUnion
  ) where

import           Reduceq.Prelude

import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Text.Prettyprint.Doc.Internal as PrettyInternal

import           Reduceq.Coq.AST
import           Reduceq.Coq.Diff
import           Reduceq.Imp.AST (getVarId)

pprintVar :: VarId -> Doc a
pprintVar (VarId index _) = parens ("tvar" <+> pretty index)

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
pprintExpr (App (App f x) y) =
  pprintApp "tapp2" [pprintExpr f, pprintExpr x, pprintExpr y]
pprintExpr (App f x) =
  pprintApp "tapp" [pprintExpr f, pprintExpr x]
pprintExpr (Abs ty _name body) =
  parens ("tabs" <+> (align . sep) [pprintTy ty, pprintExpr body])
pprintExpr (Case x ifL ifR) =
  pprintApp "tcase" [pprintExpr x, pprintExpr ifL, pprintExpr ifR]
pprintExpr (Fst x) = parens ("tfst" <+> pprintExpr x)
pprintExpr (Snd x) = parens ("tsnd" <+> pprintExpr x)
pprintExpr (Pair x y) = pprintApp "tpair" [pprintExpr x, pprintExpr y]
pprintExpr (If cond ifTrue ifFalse) =
  parens
    ("tif" <+>
     (align . sep) [pprintExpr cond, pprintExpr ifTrue, pprintExpr ifFalse])
pprintExpr (IntBinop op x y) = parens (pprintExpr x <+> op' <+> pprintExpr y)
  where
    op' =
      case op of
        IAdd -> "+"
        ISub -> "-"
        IMul -> "*"
pprintExpr (IntComp comp x y) =
  parens (pprintExpr x <+> comp' <+> pprintExpr y)
  where comp' = case comp of
          IEq -> "="
          ILt -> "<"
          IGt -> ">"
pprintExpr (Iter f x) = parens ("titer" <+> (align . sep) [pprintExpr f, pprintExpr x])
pprintExpr (Inl x) =
  parens ("tinl" <+> pprintExpr x)
pprintExpr (Inr x) =
  parens ("tinr" <+> pprintExpr x)
pprintExpr (Set arr index val) =
  parens
    ("twrite" <+>
     (align . sep) [pprintExpr arr, pprintExpr index, pprintExpr val])
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
pprintExpr (Length xs) = parens ("tlength" <+> pprintExpr xs)
pprintExpr (Range a b c) = parens ("trange" <+> (align . sep . map pprintExpr) [a,b,c])
pprintExpr (Replicate count val) =
  parens ("treplicate" <+> (align . sep) [pprintExpr count, pprintExpr val])
pprintExpr (LiftN n e) = pprintExpr e <> ".[ren (+" <> pretty n <> ")]"

pprintTypingJudgment :: Text -> [ExternReference] -> Ty -> Doc a
pprintTypingJudgment name externRefs ty =
  "empty_ctx |--" <+> pretty name <> refParams <+> "\\in" <+> pprintTy ty
  where
    refParams = hsep' (map (pretty . refName) externRefs)

pprintExternRefTyAssm :: ExternReference -> Doc a
pprintExternRefTyAssm (ExternReference name ty) =
  pprintTypingJudgment name [] ty <+> "->"

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
        (vsep (assumptions ++ [pprintTypingJudgment name externRefs ty <> "."]))
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

pprintEquivalentTheorem :: (Text -> Bool) -> [Expr] -> Text -> ProgramSteps Expr -> Either PprintError (Doc a)
pprintEquivalentTheorem isExtern argRefs name steps = do
  let (ProgramSteps initial' steps' final') =
        (stripExternLifts isExtern . instantiateExpr) <$> steps
      body =
        pprintApp "equivalent" [pprintExpr initial', pprintExpr final'] <> "."
  pure
    (vsep
       [ "Theorem" <+> pretty name <+> colon
       , indent
           2
           (vsep
              (body :
               "intros." :
               zipWith stepTo (initial' : steps') steps' ++
               [ pprintDiff
                   isExtern
                   (pruneDiff (diff (NonEmpty.last (initial' :| steps')) final'))
               , "admit."
               ]))
       , "Admitted."
       ])
  where
    stepTo :: Expr -> Expr -> Doc a
    stepTo from to =
      vsep
        [ "assert_step_to"
        , indent 2 (pprintExpr to <> ".")
        , indent
            2
            (lbrace <> indent 1 (pprintDiff isExtern (pruneDiff (diff from to))) <>
             line <>
             rbrace)
        ]
    instantiateExpr :: Expr -> Expr
    instantiateExpr e = foldl' (\expr arg -> instantiate arg expr) e argRefs

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
        (\ty' i -> pprintTypingJudgment ("arg" <> show i) [] ty' <+> "->")
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


nub :: Ord a => [a] -> [a]
nub = Set.toList . Set.fromList

pprintExternRefs :: ProgramSteps Expr -> Either PprintError ([Doc a], Text -> Bool)
pprintExternRefs steps =
  let refs = nub (collectExternReferences =<< (toList steps))
      pprintExternRef (ExternReference name ty) = pprintExternVar name ty
  in pure
       ( pprintExternRef =<< refs
       , (`Set.member` Set.fromList (map refName refs)))

pprintExternVar :: Text -> Ty -> [Doc a]
pprintExternVar name ty =
  [ "Variable" <+> pretty name <+> colon <+> "term" <> dot
  , (hang 2 . sep)
      [ "Hypothesis" <+> pretty name <> "_ty" <+> colon
      , pprintTypingJudgment name [] ty <> dot
      ]
  , "Hypothesis" <+>
    pretty name <> "_val" <+> colon <+> "value" <+> pretty name <> dot
  ]

pprintArgRefs :: ProgramSteps Expr -> Ty -> ([Expr], [Doc a], Text -> Bool)
pprintArgRefs steps ty =
  ( zipWith (\name ty' -> ExternRef (ExternReference name ty')) argNames argTys
  , concat (zipWith pprintExternVar argNames argTys)
  , (`Set.member` Set.fromList argNames))
  where
    argTys :: [Ty]
    argTys =
      let argTys' (TyFun dom cod) = dom : argTys' cod
          argTys' _ = []
      in argTys' ty
    argNames :: [Text]
    argNames =
      let argNames' (unannotate -> Abs _ name' body) = name' : argNames' body
          argNames' _ = []
      in zipWith
           (\def varId -> fromMaybe def (fmap getVarId varId))
           (map (\i -> "arg" <> show i) [1 :: Int ..])
           (argNames' (imperativeProgram steps))

pprintProofStepsObligation :: ProgramSteps Expr -> Ty -> Either PprintError (Doc a)
pprintProofStepsObligation steps ty = do
  (externRefs, isExtern) <- pprintExternRefs steps
  let (argRefs, argAssumptions, isArg) = pprintArgRefs steps ty
  equivalent <-
    pprintEquivalentTheorem
      (\n -> isExtern n || isArg n)
      argRefs
      "equivalent"
      steps
  pure
    (vsep
       (coqImports ++
        ["", "Section proof.", ""] ++
        ("(* extern references *)" : externRefs) ++
        ("(* arguments *)" : argAssumptions) ++ ["", equivalent, "End proof."]))


pprintDiff :: (Text -> Bool) -> Diff Expr -> Doc a
pprintDiff isExtern = pprintDiff' isExtern 0

inEqFun :: Text -> Expr -> Expr -> Doc a -> Doc a
inEqFun arg f g doc =
  vsep
    [ "assert" <+>
      parens
        ("HEq" <+>
         colon <+>
         "equivalent_fun" <+> (align . vsep) [pprintExpr f, pprintExpr g]) <>
      dot
    , braces
        (indent 2 $
         align $
         (vsep
            [ "intro_eq_fun_abs'" <+> pretty arg <> "."
            , "repeat simpl_noop_subst."
            , doc
            ] <>
          line))
    , "rewrite HEq."
    , "reflexivity."
    ]

-- | The integer indicates how many binders we have already traversed
pprintDiff' :: (Text -> Bool) -> Int -> Diff Expr -> Doc a
pprintDiff' _isExtern _ Equal = mempty
pprintDiff' _isExtern _ (Different x y) =
  vsep
    [ "assert" <+>
      parens
        ("HEq" <+>
         colon <+> "equivalent" <+> (align . vsep) [pprintExpr x, pprintExpr y]) <>
      dot
    , (align . vcat) [lbrace <+> "admit.", rbrace]
    , "rewrite HEq."
    , "reflexivity."
    ]
pprintDiff' isExtern !i (DifferentFun f g ty d) =
  inEqFun
    arg
    f
    g
    (pprintDiff'
       isExtern
       (i + 1)
       (stripExternLifts isExtern <$>
        substInDiff (VarId 0 Nothing) (ExternRef (ExternReference arg ty)) d))
  where
    arg = "arg" <> show i
pprintDiff' isExtern !i (DifferentArgs args) =
  vcat (map (pprintDiff' isExtern i) args)

pprintDiffs :: (Text -> Bool) -> [Diff Expr] -> Doc a
pprintDiffs isExtern = cat . punctuate (line <> "---" <> line) . map (pprintDiff isExtern)
