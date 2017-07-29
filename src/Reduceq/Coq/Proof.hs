{-# LANGUAGE ViewPatterns #-}
module Reduceq.Coq.Proof
  ( pprintExample
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

pprintTypedExpr :: TypedExpr -> Doc a
pprintTypedExpr (Ann _ e) = pprintExpr e

pprintExpr :: Expr Ty -> Doc a
pprintExpr (Var id) = pprintVar id
pprintExpr (ExternRef (ExternReference name _)) = pretty name
pprintExpr (IntLit i) =
  let lit
        | i >= 0 = pretty i
        | otherwise = parens (pretty i)
  in parens ("tint" <+> lit)
pprintExpr (App (stripAnn -> (App (stripAnn -> f) (stripAnn -> x))) (stripAnn -> y)) =
  pprintApp "tapp2" [pprintExpr f, pprintExpr x, pprintExpr y]
pprintExpr (App (stripAnn -> f) (stripAnn -> x)) =
  pprintApp "tapp" [pprintExpr f, pprintExpr x]
pprintExpr (Abs ty _name (stripAnn -> body)) =
  parens ("tabs" <+> (align . sep) [pprintTy ty, pprintExpr body])
pprintExpr (Case (stripAnn -> x) (stripAnn -> ifL) (stripAnn -> ifR)) =
  pprintApp "tcase" [pprintExpr x, pprintExpr ifL, pprintExpr ifR]
pprintExpr (Fst (stripAnn -> x)) = parens ("tfst" <+> pprintExpr x)
pprintExpr (Snd (stripAnn -> x)) = parens ("tsnd" <+> pprintExpr x)
pprintExpr (Pair (stripAnn -> x) (stripAnn -> y)) = pprintApp "tpair" [pprintExpr x, pprintExpr y]
pprintExpr (If (stripAnn -> cond) (stripAnn -> ifTrue) (stripAnn -> ifFalse)) =
  parens
    ("tif" <+>
     (align . sep) [pprintExpr cond, pprintExpr ifTrue, pprintExpr ifFalse])
pprintExpr (IntBinop op (stripAnn -> x) (stripAnn -> y)) =
  (parens . align . sep) [pprintExpr x <+> op', pprintExpr y]
  where
    op' =
      case op of
        IAdd -> "+"
        ISub -> "-"
        IMul -> "*"
pprintExpr (IntComp comp (stripAnn -> x) (stripAnn -> y)) =
  parens (pprintExpr x <+> comp' <+> pprintExpr y)
  where comp' = case comp of
          IEq -> "="
          ILt -> "<"
          IGt -> ">"
pprintExpr (Iter f x) =
  parens
    ("titer" <+>
     (align . sep) [pprintExpr (stripAnn f), pprintExpr (stripAnn x)])
pprintExpr (Inl (stripAnn -> x)) =
  parens ("tinl" <+> pprintExpr x)
pprintExpr (Inr (stripAnn -> x)) =
  parens ("tinr" <+> pprintExpr x)
pprintExpr (Set (stripAnn -> arr) (stripAnn -> index) (stripAnn -> val)) =
  parens
    ("twrite" <+>
     (align . sep) [pprintExpr arr, pprintExpr index, pprintExpr val])
pprintExpr (SetAtKey (stripAnn -> arr) (stripAnn -> key) (stripAnn -> val)) =
  pprintApp "twrite_at_key" [pprintExpr arr, pprintExpr key, pprintExpr val]
pprintExpr (Read (stripAnn -> arr) (stripAnn -> index)) =
  parens ("tread" <+> (align (sep [pprintExpr arr, pprintExpr index])))
pprintExpr (ReadAtKey (stripAnn -> arr) (stripAnn -> key)) =
  pprintApp "tread_at_key" [pprintExpr arr, pprintExpr key]
pprintExpr Unit = "tunit"
pprintExpr (Annotated e _) = pprintExpr (stripAnn e)
pprintExpr (Map (stripAnn -> f) (stripAnn -> xs)) =
  pprintApp "tmap" [pprintExpr f, pprintExpr xs]
pprintExpr (Group (stripAnn -> xs)) =
  parens ("tgroup" <+> pprintExpr xs)
pprintExpr (Fold f i xs) =
  pprintApp "tfold" [pprintExpr (stripAnn f), pprintExpr (stripAnn i), pprintExpr (stripAnn xs)]
pprintExpr (Concat xss) = parens ("tconcat" <+> pprintExpr (stripAnn xss))
pprintExpr (List xs) = parens ("tlist" <+> list (map (pprintExpr . stripAnn) xs))
pprintExpr (Length xs) = parens ("tlength" <+> pprintExpr (stripAnn xs))
pprintExpr (Range a b c) = parens ("trange" <+> (align . sep . map (pprintExpr . stripAnn)) [a,b,c])
pprintExpr (Replicate count val) =
  parens ("treplicate" <+> (align . sep) [pprintExpr (stripAnn count), pprintExpr (stripAnn val)])
pprintExpr (LiftN n e) = pprintExpr (stripAnn e) <> ".[ren (+" <> pretty n <> ")]"
pprintExpr (Zip xs ys) =
  parens ("tzip" <+> (align . sep . map (pprintExpr . stripAnn)) [xs, ys])

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

pprintTypingLemma :: Text -> Expr Ty -> Ty -> Doc a
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

pprintExprDefinition :: Text -> Expr Ty -> Doc a
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
        , "Equality"
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

pprintExample :: Expr Ty -> Ty -> Doc a
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

pprintEquivalentTheorem :: Ty -> (Text -> Bool) -> [TypedExpr] -> Text -> ProgramSteps TypedExpr -> Either PprintError (Doc a)
pprintEquivalentTheorem ty isExtern argRefs name steps = do
  let (ProgramSteps initial' steps' final') =
        (fmap (stripExternLifts isExtern) . instantiateExpr) <$> steps
      body =
        pprintApp
          ("equivalent" <+> "empty_ctx" <+> pprintTy ty)
          [pprintTypedExpr initial', pprintTypedExpr final'] <>
        "."
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
               ]))
       , "Admitted."
       ])
  where
    stepTo :: TypedExpr -> TypedExpr -> Doc a
    stepTo from to =
      vsep
        [ "assert_step_to"
        , indent 2 (pprintTypedExpr to <> ".")
        , indent
            2
            (lbrace <> indent 1 (pprintDiff isExtern (pruneDiff (diff from to))) <>
             line <>
             rbrace)
        ]
    instantiateExpr :: TypedExpr -> TypedExpr
    instantiateExpr e = foldl' (\expr arg -> instantiate arg expr) e argRefs

nub :: Ord a => [a] -> [a]
nub = Set.toList . Set.fromList

pprintExternRefs :: ProgramSteps TypedExpr -> Either PprintError ([Doc a], Text -> Bool)
pprintExternRefs steps =
  let refs = nub (collectExternReferences =<< (stripAnn <$> toList steps))
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

pprintArgRefs :: ProgramSteps TypedExpr -> [Ty] -> ([TypedExpr], [Doc a], Text -> Bool)
pprintArgRefs steps argTys =
  ( zipWith (\name ty' -> Ann ty' (ExternRef (ExternReference name ty'))) argNames argTys
  , concat (zipWith pprintExternVar argNames argTys)
  , (`Set.member` Set.fromList argNames))
  where
    argNames :: [Text]
    argNames =
      let argNames' (unannotate . stripAnn -> Abs _ name' body) = name' : argNames' body
          argNames' _ = []
      in zipWith
           (\def varId -> fromMaybe def (fmap getVarId varId))
           (map (\i -> "arg" <> show i) [1 :: Int ..])
           (argNames' (imperativeProgram steps))

splitFunTy :: Ty -> ([Ty], Ty)
splitFunTy (TyFun dom cod) = first (dom :) (splitFunTy cod)
splitFunTy t = ([], t)

pprintProofStepsObligation :: ProgramSteps TypedExpr -> Either PprintError (Doc a)
pprintProofStepsObligation steps@(ProgramSteps (Ann ty _) _ _) = do
  let (argTys, ranTy) = splitFunTy ty
  (externRefs, isExtern) <- pprintExternRefs steps
  let (argRefs, argAssumptions, isArg) = pprintArgRefs steps argTys
  equivalent <-
    pprintEquivalentTheorem
      ranTy
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


pprintDiff :: (Text -> Bool) -> Diff TypedExpr -> Doc a
pprintDiff isExtern = concatDiff . pprintDiff' isExtern 0

inEqFun :: Text -> Expr Ty -> Expr Ty -> Ty -> Ty -> Doc a -> Doc a
inEqFun arg f g dom ran doc =
  vsep
    [ (hang 2)
        ("assert" <+>
         parens
           ("equivalent_fun empty_ctx" <+>
            pprintTy dom <+>
            pprintTy ran <> line <> vsep [pprintExpr f, pprintExpr g]) <>
         dot)
    , braces
        (indent 2 $
         align $
         (vsep
            [ "intro_eq_fun_abs" <+> pretty arg <> "."
            , "repeat simpl_noop_subst."
            , doc
            ] <>
          line))
    ]

pprintMor :: Morphism -> Doc a
pprintMor MFst = "tfst_mor"
pprintMor MSnd = "tsnd_mor"
pprintMor MIter = "titer_mor"
pprintMor MApp = "tapp_mor"
pprintMor MIf = "tif_mor"
pprintMor MInl = "tinl_mor"
pprintMor MInr = "tinr_mor"
pprintMor MPair = "tpair_mor"

concatDiff :: (Doc a, Doc a) -> Doc a
concatDiff (assertion, morphism) = vcat [assertion, morphism]

-- | The integer indicates how many binders we have already traversed
pprintDiff' :: (Text -> Bool) -> Int -> Diff TypedExpr -> (Doc a, Doc a)
pprintDiff' _isExtern _ Equal = (mempty, mempty)
pprintDiff' _isExtern _ (Different x y t) =
  (vsep
    [ "assert" <+>
      parens
        (vcat
           [ "equivalent empty_ctx" <+> pprintTy t
           , indent 2 $ (align . vsep) [pprintTypedExpr x, pprintTypedExpr y]
           ]) <>
      dot
    , (align . vcat) [lbrace <+> "admit.", rbrace]
    ], mempty)
pprintDiff' isExtern !i (DifferentFun f g dom ran d) =
  ( inEqFun
      arg
      (stripAnn f)
      (stripAnn g)
      dom
      ran
      (concatDiff
         (pprintDiff'
            isExtern'
            (i + 1)
            (fmap (stripExternLifts isExtern') <$>
             substInDiff
               (VarId 0 Nothing)
               (Ann dom (ExternRef (ExternReference arg dom)))
               d)))
  , mempty)
  where
    arg = "arg" <> show i
    isExtern' var = isExtern var || var == arg
pprintDiff' isExtern !i (DifferentMor mor args) =
  let (assertions, morphisms) = unzip (map (pprintDiff' isExtern i) args)
  in ( vcat assertions
     , vcat
         ("eapply" <+>
          pprintMor mor <> "; trivial_rewrite || eauto." : morphisms))

pprintDiffs :: (Text -> Bool) -> [Diff TypedExpr] -> Doc a
pprintDiffs isExtern = cat . punctuate (line <> "---" <> line) . map (pprintDiff isExtern)
