{-# LANGUAGE ViewPatterns #-}
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
  | ErrorIn (Expr Ty)
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

guardTyEqualIn :: Expr Ty -> Ty -> Ty -> InferM TypedExpr
guardTyEqualIn e ty1 ty2 =
  if ty1 == ty2
    then pure (Ann ty1 e)
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

checkType :: Expr () -> Ty -> InferM TypedExpr
checkType (Var id) ty = do
  ty' <- varTy id
  guardTyEqualIn (Var id) ty ty'
checkType (ExternRef (ExternReference name ty')) ty =
  guardTyEqual ty' ty >> pure (Ann ty' (ExternRef (ExternReference name ty')))
checkType (IntLit i) ty = guardTyEqualIn (IntLit i) ty TyInt
checkType (App (stripAnn -> f) (stripAnn -> x)) ran = do
  x'@(Ann dom _) <- inferType x
  f' <- checkType f (TyFun dom ran)
  pure (Ann ran (App f' x'))
checkType (Abs codTy name body) ty =
  case ty of
    TyFun codTy' domTy -> do
      _ <- guardTyEqual codTy' codTy
      body' <- withBoundVar codTy (checkType (stripAnn body) domTy)
      pure (Ann ty (Abs codTy name body'))
    ty' -> throwError (ExpectedFunction ty')
checkType (Case x ifL ifR) ty = do
  x'@(Ann argTy _) <- inferType (stripAnn x)
  case argTy of
    TySum tyL tyR -> do
      ifL' <- withBoundVar tyL (checkType (stripAnn ifL) ty)
      ifR' <- withBoundVar tyR (checkType (stripAnn ifR) ty)
      pure (Ann ty (Case x' ifL' ifR'))
    ty' -> throwError (ExpectedSum ty')
checkType (Fst (stripAnn -> a)) ty = do
  a'@(Ann tyProd _) <- inferType a
  case tyProd of
    TyProd tyFst _ -> guardTyEqual tyFst ty >> pure (Ann ty (Fst a'))
    _ -> throwError (ExpectedProd tyProd)
checkType (Snd (stripAnn -> a)) ty = do
  a'@(Ann tyProd _) <- inferType a
  case tyProd of
    TyProd _ tySnd -> guardTyEqual tySnd ty >> pure (Ann ty (Snd a'))
    _ -> throwError (ExpectedProd tyProd)
checkType (Pair (stripAnn -> a) (stripAnn -> b)) ty = do
  case ty of
    TyProd tyA tyB -> do
      a' <- checkType a tyA
      b' <- checkType b tyB
      pure (Ann ty (Pair a' b'))
    _ -> throwError (ExpectedProd ty)
checkType (Inl (stripAnn -> a)) ty =
  case ty of
    TySum tyL _ -> checkType a tyL >>= \a' -> pure (Ann ty (Inl a'))
    _ -> throwError (ExpectedSum ty)
checkType (Inr (stripAnn -> a)) ty =
  case ty of
    TySum _ tyR -> checkType a tyR >>= \a' ->  pure (Ann ty (Inr a'))
    _ -> throwError (ExpectedSum ty)
checkType (If (stripAnn -> cond) (stripAnn -> ifTrue) (stripAnn -> ifFalse)) ty = do
  cond' <- checkType cond TyBool
  ifTrue' <- checkType ifTrue ty
  ifFalse' <- checkType ifFalse ty
  pure (Ann ty (If cond' ifTrue' ifFalse'))
checkType (IntBinop op (stripAnn -> x) (stripAnn -> y)) ty = do
  _ <- guardTyEqual ty TyInt
  x' <- checkType x TyInt
  y' <- checkType y TyInt
  pure (Ann ty (IntBinop op x' y'))
checkType (IntComp comp (stripAnn -> x) (stripAnn -> y)) ty = do
  _ <- guardTyEqual ty TyBool
  x' <- checkType x TyInt
  y' <- checkType y TyInt
  pure (Ann TyInt (IntComp comp x' y'))
checkType (Iter (stripAnn -> loop) (stripAnn -> init)) ty = do
  init' <- checkType init ty
  loop' <- checkType loop (TyFun ty (TySum TyUnit ty))
  pure (Ann ty (Iter loop' init'))
checkType (Set (stripAnn -> arr) (stripAnn -> index) (stripAnn -> val)) ty =
  case ty of
    TyArr tyVal -> do
      arr' <- checkType arr ty
      index' <- checkType index TyInt
      val' <- checkType val tyVal
      pure (Ann ty (Set arr' index' val'))
    _ -> throwError (ExpectedArr ty)
checkType (SetAtKey (stripAnn -> arr) (stripAnn -> key) (stripAnn -> val)) ty =
  case ty of
    TyArr (TyProd tyKey tyVal) -> do
      arr' <- checkType arr ty
      key' <- checkType key tyKey
      val' <- checkType val tyVal
      pure (Ann ty (SetAtKey arr' key' val'))
    _ -> throwError (ExpectedArr ty)
checkType (Read (stripAnn -> arr) (stripAnn -> index)) ty = do
  arr' <- checkType arr (TyArr ty)
  index' <- checkType index TyInt
  pure (Ann ty (Read arr' index'))
checkType (ReadAtKey (stripAnn -> arr) (stripAnn -> key)) ty = do
  key'@(Ann tyKey _) <- inferType key
  arr' <- checkType arr (TyProd tyKey ty)
  pure (Ann ty (ReadAtKey arr' key'))
checkType Unit ty = guardTyEqualIn Unit ty TyUnit
checkType (Annotated e ty') ty = do
  _ <- guardTyEqual ty' ty
  checkType (stripAnn e) ty
checkType (List (map stripAnn -> xs)) ty =
  case ty of
    TyArr tyEl -> do
      xs' <- traverse (`checkType` tyEl) xs
      pure (Ann ty (List xs'))
    _ -> throwError (ExpectedArr ty)
checkType (Fold (stripAnn -> f) (stripAnn -> x) (stripAnn -> xs)) ty = do
  x' <- checkType x ty
  f'@(Ann fTy _) <- inferType f
  case fTy of
    TyFun (TyProd tyAcc tyEl) tyAcc' -> do
      _ <- guardTyEqual tyAcc tyAcc'
      _ <- guardTyEqual tyAcc ty
      xs' <- checkType xs (TyArr tyEl)
      pure (Ann ty (Fold f' x' xs'))
    _ -> throwError (ExpectedFunction fTy)
checkType (LiftN n e) ty = enterLiftN n (checkType (stripAnn e) ty)
checkType (Replicate (stripAnn -> count) (stripAnn -> val)) ty =
  case ty of
    TyArr tyVal -> do
      count' <- checkType count TyInt
      val' <- checkType val tyVal
      pure (Ann ty (Replicate count' val'))
    _ -> throwError (ExpectedArr ty)
checkType e ty = do
  (Ann tyE e') <- inferType e
  guardTyEqualIn e' tyE ty

inferType :: Expr () -> InferM TypedExpr
inferType (Var id) = do
  ty <- varTy id
  pure (Ann ty (Var id))
inferType (ExternRef (ExternReference name ty)) = pure (Ann ty (ExternRef (ExternReference name ty)))
inferType (IntLit i) = pure (Ann TyInt (IntLit i))
inferType (App (stripAnn -> f) (stripAnn -> x)) = do
  f'@(Ann funTy _) <- inferType f
  case funTy of
    TyFun dom ran -> do
      x' <- checkType x dom
      pure (Ann ran (App f' x'))
    ty -> throwError (ExpectedFunction ty)
inferType (Abs dom name (stripAnn -> body)) = do
  body'@(Ann ran _) <- withBoundVar dom (inferType body)
  pure (Ann (TyFun dom ran) (Abs dom name body'))
inferType (Case (stripAnn -> x) (stripAnn -> ifL) (stripAnn -> ifR)) = do
  x'@(Ann tyX _) <- inferType x
  case tyX of
    TySum tyL tyR -> do
      ifL'@(Ann tyIfL _) <- withBoundVar tyL (inferType ifL)
      ifR'@(Ann tyIfR _) <- withBoundVar tyR (inferType ifR)
      _ <- guardTyEqual tyIfL tyIfR
      pure (Ann tyIfL (Case x' ifL' ifR'))
    _ -> throwError (ExpectedSum tyX)
inferType (Fst a) = do
  a'@(Ann ty _) <- inferType (stripAnn a)
  case ty of
    TyProd ty' _ -> pure (Ann ty' (Fst a'))
    _ -> throwError (ExpectedProd ty)
inferType (Snd a) = do
  a'@(Ann ty _) <- inferType (stripAnn a)
  case ty of
    TyProd _ ty' -> pure (Ann ty' (Snd a'))
    _ -> throwError (ExpectedProd ty)
inferType (Pair a b) = do
  a'@(Ann tyA _) <- inferType (stripAnn a)
  b'@(Ann tyB _) <- inferType (stripAnn b)
  pure (Ann (TyProd tyA tyB) (Pair a' b'))
inferType (Inl _) = throwError (AmbigousType "Cannot infer the type of `inl`.")
inferType (Inr _) = throwError (AmbigousType "Cannot infer the type of `inr`.")
inferType (If (stripAnn -> cond) (stripAnn -> ifTrue) (stripAnn -> ifFalse)) = do
  cond' <- checkType cond TyBool
  ifTrue'@(Ann ty1 _) <- inferType ifTrue
  ifFalse'@(Ann ty2 _) <- inferType ifFalse
  _ <- guardTyEqual ty1 ty2
  pure (Ann ty1 (If cond' ifTrue' ifFalse'))
inferType (IntBinop op (stripAnn -> x) (stripAnn -> y)) = do
  x' <- checkType x TyInt
  y' <- checkType y TyInt
  pure (Ann TyInt (IntBinop op x' y'))
inferType (IntComp comp x y) = do
  x' <- checkType (stripAnn x) TyInt
  y' <- checkType (stripAnn y) TyInt
  pure (Ann TyBool (IntComp comp x' y'))
inferType (Iter (stripAnn -> loop) (stripAnn -> init)) = do
  init'@(Ann ty _) <- inferType init
  loop' <- checkType loop (TyFun ty (TySum TyUnit ty))
  pure (Ann ty (Iter loop' init'))
inferType (Set (stripAnn -> arr) (stripAnn -> index) (stripAnn -> val)) = do
  index' <- checkType index TyInt
  val'@(Ann tyVal _) <- inferType val
  arr' <- checkType arr (TyArr tyVal)
  pure (Ann (TyArr tyVal) (Set arr' index' val'))
inferType (SetAtKey (stripAnn -> arr) (stripAnn -> key) (stripAnn -> val)) = do
  key'@(Ann keyTy _) <- inferType key
  val'@(Ann valTy _) <- inferType val
  let ty = TyArr (TyProd keyTy valTy)
  arr' <- checkType arr ty
  pure (Ann ty (SetAtKey arr' key' val'))
inferType (Read (stripAnn -> arr) (stripAnn -> index)) = do
  index' <- checkType index TyInt
  arr'@(Ann tyArr _) <- inferType arr
  case tyArr of
    TyArr tyVal -> pure (Ann tyVal (Read arr' index'))
    ty -> throwError (ExpectedArr ty)
inferType (ReadAtKey (stripAnn -> arr) (stripAnn -> key)) = do
  arr'@(Ann tyArr _) <- inferType arr
  case tyArr of
    TyArr (TyProd tyKey tyVal) -> do
      key' <- checkType key tyKey
      pure (Ann (TySum TyUnit tyVal) (ReadAtKey arr' key'))
    _ -> throwError (ExpectedArr tyArr)
inferType Unit = pure (Ann TyUnit Unit)
inferType (Annotated e ty) = checkType (stripAnn e) ty
inferType (Map f xs) = do
  f'@(Ann tyF _) <- inferType (stripAnn f)
  case tyF of
    TyFun tyDom tyCod -> checkType (stripAnn xs) (TyArr tyDom) >>= \xs' -> pure (Ann (TyArr tyCod) (Map f' xs'))
    _ -> throwError (ExpectedFunction tyF)
inferType (Group xs) = do
  xs'@(Ann tyXs _) <- inferType (stripAnn xs)
  case tyXs of
    TyArr argTy ->
      case argTy of
        TyProd tyK tyV -> pure (Ann (TyArr (TyProd tyK (TyArr tyV))) (Group xs'))
        _ -> throwError (ExpectedProd argTy)
    _ -> throwError (ExpectedArr tyXs)
inferType (Fold f i xs) = do
  f'@(Ann tyF _) <- inferType (stripAnn f)
  i'@(Ann tyI _) <- inferType (stripAnn i)
  case tyF of
    TyFun (TyProd tyAcc tyX) dom
      | dom == tyAcc ->
        checkType (stripAnn xs) (TyArr tyX) >>= \xs' ->
          guardTyEqual tyI tyAcc *> pure (Ann tyAcc (Fold f' i' xs'))
    _ -> throwError (ExpectedFunction tyF)
inferType (Concat xss) = do
  xss'@(Ann tyXss _) <- inferType (stripAnn xss)
  case tyXss of
    TyArr tyXs ->
      case tyXs of
        TyArr _ -> pure (Ann tyXs (Concat xss'))
        _ -> throwError (ExpectedArr tyXs)
    _ -> throwError (ExpectedArr tyXss)
inferType (List xss) = do
  xss' <- traverse inferType (map stripAnn xss)
  let tys = map (\(Ann t _) -> t) xss'
  case tys of
    (t:ts) -> traverse_ (guardTyEqual t) ts *> pure (Ann (TyArr t) (List xss'))
    _ -> panic "Cannot infer type of empty list literal"
inferType (Length xs) = do
  xs'@(Ann ty _) <- inferType (stripAnn xs)
  case ty of
    TyArr _ -> pure (Ann TyInt (Length xs'))
    _ -> throwError (ExpectedArr ty)
inferType (Range (stripAnn -> a) (stripAnn -> b) (stripAnn -> c)) = do
  a' <- checkType a TyInt
  b' <- checkType b TyInt
  c' <- checkType c TyInt
  pure (Ann (TyArr TyInt) (Range a' b' c'))
inferType (Replicate (stripAnn -> count) val) = do
  count' <- checkType count TyInt
  val'@(Ann tyVal _) <- inferType (stripAnn val)
  pure (Ann (TyArr tyVal) (Replicate count' val'))
inferType (LiftN n e) = do
  enterLiftN n (inferType (stripAnn e))

inferStepsType :: ProgramSteps (Expr ()) -> InferM (ProgramSteps TypedExpr)
inferStepsType (ProgramSteps initial steps final) = do
  initial' <- inferType initial
  steps' <- traverse inferType steps
  final' <- inferType final
  foldM_
    (\(Ann ty e) (Ann ty' _) -> guardTyEqualIn e ty ty')
    initial'
    (final' : steps')
  pure (ProgramSteps initial' steps' final')
