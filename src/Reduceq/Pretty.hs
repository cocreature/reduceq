{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Reduceq.Pretty
  ( displayDoc
  , displayCompact
  , pprintExpr
  , PprintM
  , runPprintM
  ) where

import           Reduceq.Prelude

import qualified Data.Map as Map
import           Data.Text.Prettyprint.Doc hiding ((<>))
import           Data.Text.Prettyprint.Doc.Render.Terminal (Color(..), color, AnsiTerminal)
import           Data.Text.Prettyprint.Doc.Render.Text

import           Reduceq.CoqAST

type VarColors = Map VarId Color

newtype PprintM a = PprintM (StateT Color (Reader VarColors) a)
  deriving (Functor, Applicative, Monad, MonadState Color, MonadReader VarColors)

runPprintM :: PprintM a -> a
runPprintM (PprintM a) =
  runReader (evalStateT a Red) Map.empty

shiftVarMap :: VarColors -> VarColors
shiftVarMap = Map.mapKeys succ

withBoundVar :: (Color -> PprintM a) -> PprintM a
withBoundVar x = do
  c <- get
  put (nextColor c)
  local (Map.insert (VarId 0) c . shiftVarMap) (x c)

coloredVar :: VarId -> PprintM (Doc AnsiTerminal)
coloredVar id@(VarId index) = do
  c <- asks (Map.lookup id)
  case c of
    Nothing -> panic ("Unknown variable index: " <> show id)
    Just c' -> (pure . color c' . pretty @Text) ("v" <> show index)

nextColor :: Color -> Color
nextColor Red = Green
nextColor Green = Yellow
nextColor Yellow = Blue
nextColor Blue = Magenta
nextColor Magenta = Cyan
nextColor Cyan = Red
nextColor _ = panic "Can only cycle between visible colors"

pprintTy :: Ty -> Doc a
pprintTy TyInt = "Int"
pprintTy TyBool = "Bool"
pprintTy TyUnit = "()"
pprintTy (TyProd x y) = pprintTy x <+> "*" <+> pprintTy y
pprintTy (TyArr t) = brackets (pprintTy t)

pprintOp :: IntBinop -> Doc a
pprintOp IAdd = "+"
pprintOp IMul = "*"
pprintOp ISub = "-"

pprintComp :: IntComp -> Doc a
pprintComp IEq = "="
pprintComp ILt = "<"
pprintComp IGt = ">"

pprintExpr :: Expr -> PprintM (Doc AnsiTerminal)
pprintExpr (Var id) = coloredVar id
pprintExpr (IntLit i)
  | i >= 0 = pure (pretty i)
  | otherwise = (pure . parens . pretty) i
pprintExpr (App f x) =
  parens . align . sep <$> sequence [pprintExpr f, pprintExpr x]
pprintExpr (Abs ty body) =
  withBoundVar $ \c ->
    parens . hang 2 . sep <$>
    sequence
      [ pure ("fun" <+> color c "▢" <+> ":" <+> pprintTy ty <> ".")
      , pprintExpr body
      ]
pprintExpr (Fst x) = parens . ("fst" <+>) <$> pprintExpr x
pprintExpr (Snd x) = parens . ("snd" <+>) <$> pprintExpr x
pprintExpr (Pair x y) =
  liftA2 (\a b -> parens (a <> "," <+> b)) (pprintExpr x) (pprintExpr y)
pprintExpr (If cond ifTrue ifFalse) =
  parens . hang 3 . sep <$>
  sequence
    [("if" <+>) <$> pprintExpr cond, pprintExpr ifTrue, pprintExpr ifFalse]
pprintExpr (IntBinop op x y) =
  parens . hsep <$> sequence [pprintExpr x, pure (pprintOp op), pprintExpr y]
pprintExpr (IntComp comp x y) =
  parens . hsep <$>
  sequence [pprintExpr x, pure (pprintComp comp), pprintExpr y]
pprintExpr (Iter f x) =
  parens . hsep <$> sequence [pure "iter", pprintExpr f, pprintExpr x]
pprintExpr (Inl x) = parens . ("inl" <+>) <$> pprintExpr x
pprintExpr (Inr x) = parens . ("inr" <+>) <$> pprintExpr x
pprintExpr Unit = pure "()"

displayDoc :: Doc a -> Text
displayDoc = renderStrict . layoutPretty defaultLayoutOptions . unAnnotate

displayCompact :: Doc a -> Text
displayCompact =
  renderStrict .
  layoutPretty (defaultLayoutOptions {layoutPageWidth = Unbounded}) . unAnnotate
