{-# LANGUAGE ViewPatterns #-}
module Reduceq.Coq.Pretty
  ( displayDoc
  , displayCompact
  , pprintExpr
  , pprintTy
  , PprintM
  , runPprintM
  , AnsiStyle
  ) where

import           Reduceq.Prelude

import qualified Data.Map as Map
import           Data.Text.Prettyprint.Doc hiding ((<>))
import           Data.Text.Prettyprint.Doc.Render.Terminal
       (AnsiStyle, Color(..), bold, color)
import           Data.Text.Prettyprint.Doc.Render.Text

import           Reduceq.Coq.AST

type VarColors = Map VarId Color

newtype PprintM a =
  PprintM (StateT [Color] (Reader VarColors) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadState [Color]
           , MonadReader VarColors
           )

runPprintM :: PprintM a -> a
runPprintM (PprintM a) = runReader (evalStateT a varIdColors) Map.empty

shiftVarMap :: VarColors -> VarColors
shiftVarMap = Map.mapKeys succ

withBoundVar :: (Color -> PprintM a) -> PprintM a
withBoundVar x = do
  (c:cs) <- get
  put cs
  local (Map.insert (VarId 0 Nothing) c . shiftVarMap) (x c)

coloredVar :: VarId -> PprintM (Doc AnsiStyle)
coloredVar id@(VarId index _) = do
  c <- asks (Map.lookup id)
  case c of
    Nothing -- It is possible that there are free variables in an expression
     -> (pure . annotate bold . pretty @Text) ("v" <> show index)
    Just c' -> (pure . annotate (color c') . pretty @Text) ("v" <> show index)

varIdColors :: [Color]
varIdColors = cycle [Red, Green, Yellow, Blue, Magenta, Cyan]

pprintTy :: Ty -> Doc a
pprintTy TyInt = "Int"
pprintTy TyReal = "Real"
pprintTy TyBool = "Bool"
pprintTy TyUnit = "()"
pprintTy (TyProd x y) = parens (pprintTy x <+> "*" <+> pprintTy y)
pprintTy (TySum x y) = pprintTy x <+> "+" <+> pprintTy y
pprintTy (TyArr t) = brackets (pprintTy t)
pprintTy (TyFun cod dom) = pprintTy cod <+> "→" <+> pprintTy dom

pprintOp :: IntBinop -> Doc a
pprintOp IAdd = "+"
pprintOp IMul = "*"
pprintOp ISub = "-"

pprintComp :: IntComp -> Doc a
pprintComp IEq = "="
pprintComp ILt = "<"
pprintComp IGt = ">"

pprintExpr :: Expr a -> PprintM (Doc AnsiStyle)
pprintExpr (Var id) = coloredVar id
pprintExpr (IntLit i)
  | i >= 0 = pure (pretty i)
  | otherwise = (pure . parens . pretty) i
pprintExpr (App (stripAnn -> f) (stripAnn -> x)) =
  parens . align . sep <$>
  sequence [pprintExpr f, pprintExpr x]
pprintExpr (Abs ty _name body) =
  withBoundVar $ \c ->
    parens . hang 2 . sep <$>
    sequence
      [ pure ("fun" <+> annotate (color c) "▢" <+> ":" <+> pprintTy ty <> ".")
      , pprintExpr (stripAnn body)
      ]
pprintExpr (Case (stripAnn -> x) (stripAnn -> ifL) (stripAnn -> ifR)) = do
  x' <- pprintExpr x
  ifL' <- withBoundVar (\_ -> pprintExpr ifL)
  ifR' <- withBoundVar (\_ -> pprintExpr ifR)
  (pure . parens . hang 3 . sep) ["case" <+> x', ifL', ifR']
pprintExpr (Fst (stripAnn -> x)) = parens . ("fst" <+>) <$> pprintExpr x
pprintExpr (Snd (stripAnn -> x)) = parens . ("snd" <+>) <$> pprintExpr x
pprintExpr (Pair (stripAnn -> x) (stripAnn -> y)) =
  liftA2 (\a b -> parens (a <> "," <+> b)) (pprintExpr x) (pprintExpr y)
pprintExpr (If (stripAnn -> cond) (stripAnn -> ifTrue) (stripAnn -> ifFalse)) =
  parens . hang 3 . sep <$>
  sequence
    [("if" <+>) <$> pprintExpr cond, pprintExpr ifTrue, pprintExpr ifFalse]
pprintExpr (IntBinop op (stripAnn -> x) (stripAnn -> y)) =
  parens . hsep <$> sequence [pprintExpr x, pure (pprintOp op), pprintExpr y]
pprintExpr (IntComp comp (stripAnn -> x) (stripAnn -> y)) =
  parens . hsep <$>
  sequence [pprintExpr x, pure (pprintComp comp), pprintExpr y]
pprintExpr (Iter (stripAnn -> f) (stripAnn -> x)) =
  parens . hsep <$> sequence [pure "iter", pprintExpr f, pprintExpr x]
pprintExpr (Inl(stripAnn -> x)) = parens . ("inl" <+>) <$> pprintExpr x
pprintExpr (Inr(stripAnn -> x)) = parens . ("inr" <+>) <$> pprintExpr x
pprintExpr (Set (stripAnn -> arr) (stripAnn -> index) (stripAnn -> val)) =
  liftA3
    (\arr' index' val' -> parens ("set" <+> arr' <+> index' <+> val'))
    (pprintExpr arr)
    (pprintExpr index)
    (pprintExpr val)
pprintExpr (SetAtKey (stripAnn -> arr) (stripAnn -> index) (stripAnn -> val)) =
  liftA3
    (\arr' index' val' -> parens ("set_at_key" <+> arr' <+> index' <+> val'))
    (pprintExpr arr)
    (pprintExpr index)
    (pprintExpr val)
pprintExpr (Read (stripAnn -> arr) (stripAnn -> index)) =
  liftA2
    (\arr' index' -> parens ("read" <+> arr' <+> index'))
    (pprintExpr arr)
    (pprintExpr index)
pprintExpr (ReadAtKey (stripAnn -> m) (stripAnn -> key)) =
  liftA2
    (\m' k -> parens ("read_at_key" <+> m' <+> k))
    (pprintExpr m)
    (pprintExpr key)
pprintExpr Unit = pure "()"
pprintExpr (ExternRef (ExternReference name _)) = pure (pretty name)
pprintExpr (Annotated e _) = pprintExpr (stripAnn e)
pprintExpr (Map (stripAnn -> f) (stripAnn -> xs)) = do
  f' <- pprintExpr f
  xs' <- pprintExpr xs
  (pure . parens . hang 3 . sep) ["map", f', xs']
pprintExpr (Group (stripAnn -> xs)) = do
  xs' <- pprintExpr xs
  (pure . parens . hang 3 . sep) ["group", xs']
pprintExpr (Concat (stripAnn -> xss)) = do
  xss' <- pprintExpr xss
  (pure . parens . hang 3 . sep) ["concat", xss']
pprintExpr (Fold (stripAnn -> f) (stripAnn -> i) (stripAnn -> xs)) = do
  f' <- pprintExpr f
  i' <- pprintExpr i
  xs' <- pprintExpr xs
  (pure . parens . hang 3 . sep) ["fold", f', i', xs']
pprintExpr (List (map stripAnn -> xs)) =
  list <$> mapM pprintExpr xs
pprintExpr (Length (stripAnn -> xs)) = (parens . ("length" <+>)) <$> pprintExpr xs
pprintExpr (Range (stripAnn -> a) (stripAnn -> b) (stripAnn -> c)) = do
  a' <- pprintExpr a
  b' <- pprintExpr b
  c' <- pprintExpr c
  pure (parens ("trange" <+> a' <+> b' <+> c'))
pprintExpr (Replicate (stripAnn -> count) (stripAnn -> val)) = do
  count' <- pprintExpr count
  val' <- pprintExpr val
  pure (parens ("treplicate" <+> (align . sep) [count', val']))
pprintExpr (LiftN _ e) = pprintExpr (stripAnn e)

displayDoc :: Doc a -> Text
displayDoc =
  renderStrict .
  layoutPretty (LayoutOptions (AvailablePerLine 100 0.8)) . unAnnotate

displayCompact :: Doc a -> Text
displayCompact =
  renderStrict .
  layoutPretty (defaultLayoutOptions {layoutPageWidth = Unbounded}) . unAnnotate
