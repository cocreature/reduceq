module Reduceq.Coq.Typing
  ( inferType
  , runInferM
  , InferM
  , InferError(..)
  , showInferError
  ) where

import           Reduceq.Prelude

import qualified Data.Map as Map
import           Reduceq.Coq.AST

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
  = TypeMismatch Ty Ty
  | UnboundVariable VarId
  | AmbigousType Text
  | ExpectedFunction Ty
  | ExpectedProd Ty
  | ExpectedBool Ty
  | ExpectedInt Ty
  | ExpectedArr Ty
  deriving (Show, Eq, Ord)

showInferError :: InferError -> Text
showInferError = show

data TypedVar =
  TypedVar !VarId
           !Ty
  deriving (Show, Eq, Ord)

shiftVarMap :: VarContext -> VarContext
shiftVarMap = Map.mapKeys succ

withBoundVar :: Ty -> InferM a -> InferM a
withBoundVar ty = local (Map.insert (VarId 0) ty . shiftVarMap)

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

checkType :: Expr VarId -> Ty -> InferM Ty
checkType (Var id) ty = do
  ty' <- varTy id
  guardTyEqual ty ty'
checkType (ExternRef (ExternReference _ ty')) ty = guardTyEqual ty' ty
checkType (IntLit _) ty = guardTyEqual ty TyInt
checkType (App f x) ty = do
  argTy <- inferType x
  _ <- checkType f (TyFun argTy ty)
  pure ty
checkType (Abs codTy body) ty =
  case ty of
    TyFun codTy' domTy -> do
      _ <- guardTyEqual codTy' codTy
      _ <- withBoundVar codTy (checkType body domTy)
      pure ty
    ty' -> throwError (ExpectedFunction ty')
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
checkType (Inr a) ty =
  case ty of
    TySum _ tyR -> checkType a tyR *> pure ty
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
checkType (Read arr index) ty = do
  _ <- checkType arr (TyArr ty)
  _ <- checkType index TyInt
  pure ty
checkType Unit ty = guardTyEqual ty TyUnit
checkType (Annotated e ty') ty = do
  _ <- guardTyEqual ty' ty
  checkType e ty

inferType :: Expr VarId -> InferM Ty
inferType (Var id) = varTy id
inferType (IntLit _) = pure TyInt
inferType (App f x) = do
  funTy <- inferType f
  case funTy of
    TyFun cod dom ->
      checkType x cod *> pure dom
    ty -> throwError (ExpectedFunction ty)
inferType (Abs codTy body) = do
  domTy <- withBoundVar codTy (inferType body)
  pure (TyFun codTy domTy)
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
inferType (Read arr index) = do
  _ <- checkType index TyInt
  tyArr <- inferType arr
  case tyArr of
    TyArr tyVal -> pure tyVal
    ty -> throwError (ExpectedArr ty)
inferType Unit = pure TyUnit
inferType (Annotated e ty) = checkType e ty
