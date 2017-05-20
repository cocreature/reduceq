module Reduceq.Pretty
  ( displayDoc
  , displayCompact
  , pprintExpr
  , pprintTy
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
  local (Map.insert (VarId 0) c . shiftVarMap) (x c)

coloredVar :: VarId -> PprintM (Doc AnsiTerminal)
coloredVar id@(VarId index) = do
  c <- asks (Map.lookup id)
  case c of
    Nothing -> panic ("Unknown variable index: " <> show id)
    Just c' -> (pure . color c' . pretty @Text) ("v" <> show index)

varIdColors :: [Color]
varIdColors = cycle [Red, Green, Yellow, Blue, Magenta, Cyan, Red]

pprintTy :: Ty -> Doc a
pprintTy TyInt = "Int"
pprintTy TyReal = "Real"
pprintTy TyBool = "Bool"
pprintTy TyUnit = "()"
pprintTy (TyProd x y) = pprintTy x <+> "*" <+> pprintTy y
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

pprintExpr :: Expr VarId -> PprintM (Doc AnsiTerminal)
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
pprintExpr (Set arr index val) =
  liftA3
    (\arr' index' val' -> parens ("set" <+> arr' <+> index' <+> val'))
    (pprintExpr arr)
    (pprintExpr index)
    (pprintExpr val)
pprintExpr (SetAtKey arr index val) =
  liftA3
    (\arr' index' val' -> parens ("set_at_key" <+> arr' <+> index' <+> val'))
    (pprintExpr arr)
    (pprintExpr index)
    (pprintExpr val)
pprintExpr (Read arr index) =
  liftA2
    (\arr' index' -> parens ("read" <+> arr' <+> index'))
    (pprintExpr arr)
    (pprintExpr index)
pprintExpr (ReadAtKey m key) =
  liftA2
    (\m' k -> parens ("read_at_key" <+> m' <+> k))
    (pprintExpr m)
    (pprintExpr key)
pprintExpr Unit = pure "()"
pprintExpr (ExternRef (ExternReference name _)) = pure (pretty name)
pprintExpr (Annotated e _) = pprintExpr e

displayDoc :: Doc a -> Text
displayDoc = renderStrict . layoutPretty defaultLayoutOptions . unAnnotate

displayCompact :: Doc a -> Text
displayCompact =
  renderStrict .
  layoutPretty (defaultLayoutOptions {layoutPageWidth = Unbounded}) . unAnnotate
