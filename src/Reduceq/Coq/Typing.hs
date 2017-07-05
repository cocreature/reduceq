module Reduceq.Coq.Typing
  ( inferType
  , inferStepsType
  , runInferM
  , InferM
  , InferError(..)
  , showInferError
  ) where

import           Reduceq.Prelude

import qualified Data.Map as Map
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Terminal

import           Reduceq.Coq.AST
import           Reduceq.Coq.Pretty

type VarContext = Map VarId Ty

newtype InferM a =
  InferM (ExceptT InferError (Reader VarContext) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader VarContext
           , MonadError InferError
           )

runInferM :: InferM a -> Either InferError a
runInferM (InferM x) = runReader (runExceptT x) Map.empty

data InferError
  = TypeMismatch Ty
                 Ty
  | ErrorIn Expr
            InferError
  | UnboundVariable VarId
  | AmbigousType Text
  | ExpectedFunction Ty
  | ExpectedSum Ty
  | ExpectedProd Ty
  | ExpectedBool Ty
  | ExpectedInt Ty
  | ExpectedArr Ty
  deriving (Show, Eq, Ord)

showInferError :: InferError -> Doc AnsiStyle
showInferError (ErrorIn e err) =
  vsep
    [ "Type error:" <+> showInferError err
    , "in expression:" <+> hang 4 (runPprintM (pprintExpr e))
    ]
showInferError (TypeMismatch actual expected) =
  (hang 4 . sep)
    [ "Type mismatch:"
    , "expected" <+> annotate bold (pprintTy expected)
    , "but got" <+> annotate bold (pprintTy actual) <> "."
    ]
showInferError err = pretty (show err :: Text)

data TypedVar =
  TypedVar !VarId
           !Ty
  deriving (Show, Eq, Ord)

shiftVarMap :: VarContext -> VarContext
shiftVarMap = Map.mapKeys succ

enterLiftN :: Word -> InferM a -> InferM a
enterLiftN n =
  local
    (Map.mapKeys (\(VarId i name) -> VarId (i - n) name) .
     Map.filterWithKey (\k _ -> k >= VarId n Nothing))

withBoundVar :: Ty -> InferM a -> InferM a
withBoundVar ty = local (Map.insert (VarId 0 Nothing) ty . shiftVarMap)

guardTyEqualIn :: Expr -> Ty -> Ty -> InferM Ty
guardTyEqualIn e ty1 ty2 =
  if ty1 == ty2
    then pure ty1
    else throwError (ErrorIn e (TypeMismatch ty1 ty2))

guardTyEqual :: Ty -> Ty -> InferM Ty
guardTyEqual ty1 ty2 =
  if ty1 == ty2
    then pure ty1
    else throwError (TypeMismatch ty1 ty2)

varTy :: VarId -> InferM Ty
varTy id = do
  ty <- asks (Map.lookup id)
  case ty of
    Nothing -> throwError (UnboundVariable id)
    Just ty' -> pure ty'

checkType :: Expr -> Ty -> InferM Ty
checkType (Var id) ty = do
  ty' <- varTy id
  guardTyEqualIn (Var id) ty ty'
checkType (ExternRef (ExternReference _ ty')) ty = guardTyEqual ty' ty
checkType lit@(IntLit _) ty = guardTyEqualIn lit ty TyInt
checkType (App f x) ty = do
  argTy <- inferType x
  _ <- checkType f (TyFun argTy ty)
  pure ty
checkType (Abs codTy _name body) ty =
  case ty of
    TyFun codTy' domTy -> do
      _ <- guardTyEqual codTy' codTy
      _ <- withBoundVar codTy (checkType body domTy)
      pure ty
    ty' -> throwError (ExpectedFunction ty')
checkType (Case x ifL ifR) ty = do
  argTy <- inferType x
  case argTy of
    TySum tyL tyR -> do
      _ <- withBoundVar tyL (checkType ifL ty)
      _ <- withBoundVar tyR (checkType ifR ty)
      pure ty
    ty' -> throwError (ExpectedSum ty')
checkType (Fst a) ty = do
  tyProd <- inferType a
  case tyProd of
    TyProd tyFst _ -> guardTyEqual tyFst ty
    _ -> throwError (ExpectedProd tyProd)
checkType (Snd a) ty = do
  tyProd <- inferType a
  case tyProd of
    TyProd _ tySnd -> guardTyEqual tySnd ty
    _ -> throwError (ExpectedProd tyProd)
checkType (Pair a b) ty = do
  case ty of
    TyProd tyA tyB -> do
      _ <- checkType a tyA
      _ <- checkType b tyB
      pure ty
    _ -> throwError (ExpectedProd ty)
checkType (Inl a) ty =
  case ty of
    TySum tyL _ -> checkType a tyL *> pure ty
    _ -> throwError (ExpectedSum ty)
checkType (Inr a) ty =
  case ty of
    TySum _ tyR -> checkType a tyR *> pure ty
    _ -> throwError (ExpectedSum ty)
checkType (If cond ifTrue ifFalse) ty = do
  _ <- checkType cond TyBool
  _ <- checkType ifTrue ty
  _ <- checkType ifFalse ty
  pure ty
checkType (IntBinop _ x y) ty = do
  _ <- guardTyEqual ty TyInt
  _ <- checkType x TyInt
  _ <- checkType y TyInt
  pure TyInt
checkType (IntComp _ x y) ty = do
  _ <- guardTyEqual ty TyBool
  _ <- checkType x TyInt
  _ <- checkType y TyInt
  pure TyInt
checkType (Iter loop init) ty = do
  _ <- checkType init ty
  _ <- checkType loop (TyFun ty (TySum TyUnit ty))
  pure ty
checkType (Set arr index val) ty =
  case ty of
    TyArr tyVal -> do
      _ <- checkType arr ty
      _ <- checkType index TyInt
      _ <- checkType val tyVal
      pure ty
    _ -> throwError (ExpectedArr ty)
checkType (SetAtKey arr key val) ty =
  case ty of
    TyArr (TyProd tyKey tyVal) -> do
      _ <- checkType arr ty
      _ <- checkType key tyKey
      _ <- checkType val tyVal
      pure ty
    _ -> throwError (ExpectedArr ty)
checkType (Read arr index) ty = do
  _ <- checkType arr (TyArr ty)
  _ <- checkType index TyInt
  pure ty
checkType (ReadAtKey arr key) ty = do
  tyKey <- inferType key
  _ <- checkType arr (TyProd tyKey ty)
  pure (TySum TyUnit ty)
checkType Unit ty = guardTyEqual ty TyUnit
checkType (Annotated e ty') ty = do
  _ <- guardTyEqual ty' ty
  checkType e ty
checkType (List xs) ty =
  case ty of
    TyArr tyEl ->
      ty <$ traverse_ (`checkType` tyEl) xs
    _ -> throwError (ExpectedArr ty)
checkType (Fold f x xs) ty = do
  _ <- checkType x ty
  fTy <- inferType f
  case fTy of
    TyFun (TyProd tyAcc tyEl) tyAcc' -> do
      _ <- guardTyEqual tyAcc tyAcc'
      _ <- guardTyEqual tyAcc ty
      _ <- checkType xs (TyArr tyEl)
      pure tyAcc
    _ -> throwError (ExpectedFunction fTy)
checkType (LiftN n e) ty = enterLiftN n (checkType e ty)
checkType e ty = do
  tyE <- inferType e
  guardTyEqualIn e tyE ty

inferType :: Expr -> InferM Ty
inferType (Var id) = varTy id
inferType (ExternRef (ExternReference _ ty)) = pure ty
inferType (IntLit _) = pure TyInt
inferType (App f x) = do
  funTy <- inferType f
  case funTy of
    TyFun cod dom ->
      checkType x cod *> pure dom
    ty -> throwError (ExpectedFunction ty)
inferType (Abs codTy _name body) = do
  domTy <- withBoundVar codTy (inferType body)
  pure (TyFun codTy domTy)
inferType (Case x ifL ifR) = do
  tyX <- inferType x
  case tyX of
    TySum tyL tyR -> do
      tyIfL <- withBoundVar tyL (inferType ifL)
      tyIfR <- withBoundVar tyR (inferType ifR)
      guardTyEqual tyIfL tyIfR
    _ -> throwError (ExpectedSum tyX)
inferType (Fst a) = do
  ty <- inferType a
  case ty of
    TyProd ty' _ -> pure ty'
    _ -> throwError (ExpectedProd ty)
inferType (Snd a) = do
  ty <- inferType a
  case ty of
    TyProd _ ty' -> pure ty'
    _ -> throwError (ExpectedProd ty)
inferType (Pair a b) = TyProd <$> inferType a <*> inferType b
inferType (Inl _) = throwError (AmbigousType "Cannot infer the type of `inl`.")
inferType (Inr _) = throwError (AmbigousType "Cannot infer the type of `inr`.")
inferType (If cond ifTrue ifFalse) = do
  _ <- checkType cond TyBool
  ty1 <- inferType ifTrue
  ty2 <- inferType ifFalse
  guardTyEqual ty1 ty2
inferType (IntBinop _ x y) = do
  _ <- checkType x TyInt
  _ <- checkType y TyInt
  pure TyInt
inferType (IntComp _ x y) = do
  _ <- checkType x TyInt
  _ <- checkType y TyInt
  pure TyBool
inferType (Iter loop init) = do
  ty <- inferType init
  _ <- checkType loop (TyFun ty (TySum TyUnit ty))
  pure ty
inferType (Set arr index val) = do
  _ <- checkType index TyInt
  tyVal <- inferType val
  checkType arr (TyArr tyVal)
inferType (SetAtKey arr key val) = do
  keyTy <- inferType key
  valTy <- inferType val
  checkType arr (TyArr (TyProd keyTy valTy))
inferType (Read arr index) = do
  _ <- checkType index TyInt
  tyArr <- inferType arr
  case tyArr of
    TyArr tyVal -> pure tyVal
    ty -> throwError (ExpectedArr ty)
inferType (ReadAtKey arr key) = do
  tyArr <- inferType arr
  case tyArr of
    TyArr (TyProd tyKey tyVal) -> do
      _ <- checkType key tyKey
      pure (TySum TyUnit tyVal)
    _ -> throwError (ExpectedArr tyArr)
inferType Unit = pure TyUnit
inferType (Annotated e ty) = checkType e ty
inferType (Map f xs) = do
  tyF <- inferType f
  case tyF of
    TyFun tyDom tyCod -> checkType xs (TyArr tyDom) *> pure (TyArr tyCod)
    _ -> throwError (ExpectedFunction tyF)
inferType (Group xs) = do
  tyXs <- inferType xs
  case tyXs of
    TyArr argTy ->
      case argTy of
        TyProd tyK tyV -> pure (TyArr (TyProd tyK (TyArr tyV)))
        _ -> throwError (ExpectedProd argTy)
    _ -> throwError (ExpectedArr tyXs)
inferType (Fold f i xs) = do
  tyF <- inferType f
  tyI <- inferType i
  case tyF of
    TyFun (TyProd tyAcc tyX) dom
      | dom == tyAcc ->
        checkType xs (TyArr tyX) *> guardTyEqualIn i tyI tyAcc *> pure tyAcc
    _ -> throwError (ExpectedFunction tyF)
inferType (Concat xss) = do
  tyXss <- inferType xss
  case tyXss of
    TyArr tyXs ->
      case tyXs of
        TyArr _ -> pure tyXs
        _ -> throwError (ExpectedArr tyXs)
    _ -> throwError (ExpectedArr tyXss)
inferType (List xss) = do
  tys <- traverse inferType xss
  case tys of
    (t:ts) -> traverse_ (guardTyEqual t) ts *> pure (TyArr t)
    _ -> panic "Cannot infer type of empty list literal"
inferType (Length xs) = do
  ty <- inferType xs
  case ty of
    TyArr _ -> pure TyInt
    _ -> throwError (ExpectedArr ty)
inferType (Range a b c) = do
  _ <- checkType a TyInt
  _ <- checkType b TyInt
  _ <- checkType c TyInt
  pure (TyArr TyInt)
inferType (LiftN n e) = do
  enterLiftN n (inferType e)

inferStepsType :: ProgramSteps Expr -> InferM Ty
inferStepsType (ProgramSteps initial steps final) = do
  initialTy <- inferType initial
  stepsTys <- traverse inferType steps
  finalTy <- inferType final
  foldlM
    (\ty (expr, ty') -> guardTyEqualIn expr ty ty')
    initialTy
    ((final, finalTy) :| zip steps stepsTys)
