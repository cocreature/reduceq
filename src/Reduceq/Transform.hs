{-# LANGUAGE OverloadedLists #-}
module Reduceq.Transform
  ( runTransformM
  , transformDecl
  , transformDecls
  , TransformError(..)
  , showTransformError
  ) where

import           Reduceq.Prelude

import qualified Data.List.NonEmpty as NonEmpty
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set

import qualified Reduceq.Coq as Coq
import qualified Reduceq.Imp as Imp

type VarContext = Map Imp.VarId (Coq.Expr Coq.VarId, Imp.Ty)

data TransformError
  = UnknownVariable Imp.VarId
  | MissingReturnStmt
  | ExpectedArgs Imp.VarId
                 !Int
                 !Int
  deriving (Show, Eq, Ord)

showTransformError :: TransformError -> Text
showTransformError (UnknownVariable (Imp.VarId id)) =
  "Unknown variable " <> show id <>
  ". Variables can only be referenced after they have been declared or if they are function parameters"
showTransformError MissingReturnStmt =
  "Missing return statement: Each function needs to end with a return statement."
showTransformError (ExpectedArgs (Imp.VarId name) expected actual) =
  show name <> " expects " <> show expected <> " arguments but got " <>
  show actual <>
  "."

newtype TransformM a =
  TransformM (ExceptT TransformError (Reader VarContext) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader VarContext
           , MonadError TransformError
           )

withBoundVar :: Imp.TypedVar -> TransformM (Coq.Expr Coq.VarId) -> TransformM (Coq.Expr Coq.VarId)
withBoundVar (Imp.TypedVar name ty) =
  local
    (Map.insert name (Coq.Var $ Coq.VarId 0, ty) .
     Map.map (first Coq.shiftVars)) .
  fmap (Coq.Abs (transformTy ty))

withAnonBoundVar :: Coq.Ty -> TransformM (Coq.Expr Coq.VarId) -> TransformM (Coq.Expr Coq.VarId)
withAnonBoundVar ty = local (Map.map (first Coq.shiftVars)) . fmap (Coq.Abs ty)

withBoundVarProd :: (Imp.TypedVar, Imp.TypedVar) -> TransformM (Coq.Expr Coq.VarId) -> TransformM (Coq.Expr Coq.VarId)
withBoundVarProd (Imp.TypedVar fstName fstTy, Imp.TypedVar sndName sndTy) =
  assert (fstName /= sndName) $
  local
    (Map.insert fstName (Coq.Fst (Coq.Var (Coq.VarId 0)), fstTy) .
     Map.insert sndName (Coq.Snd (Coq.Var (Coq.VarId 0)), sndTy)) .
  fmap (Coq.Abs (Coq.TyProd (transformTy fstTy) (transformTy sndTy)))

varRef :: Imp.VarId -> TransformM (Coq.Expr Coq.VarId)
varRef id = do
  expr <- asks (Map.lookup id)
  case expr of
    Nothing -> throwError (UnknownVariable id)
    Just (e, _) -> pure e

runTransformM :: TransformM a -> Either TransformError a
runTransformM (TransformM a) = runReader (runExceptT a) Map.empty

transformDecl :: Imp.FunDecl -> TransformM (Coq.Expr Coq.VarId)
transformDecl (Imp.FunctionDeclaration (Imp.VarId name) args retTy body) =
  case body of
    Imp.ExternFunction
      -- TODO this needs to be lifted by the number of bound variables
     ->
      pure
        (Coq.Annotated
           (Coq.ExternRef (Coq.ExternReference name coqTy))
           coqTy)
    Imp.FunctionBody stmts ->
      (`Coq.Annotated` coqTy) <$>
      foldr (.) identity (map withBoundVar args) (transformStmts stmts)
  where
    coqTy = transformTy (Imp.TyFun (map Imp.varType args) retTy)

transformDecls :: NonEmpty Imp.FunDecl -> TransformM (Coq.Expr Coq.VarId)
transformDecls decls
 -- declarations can only reference earlier declarations
 =
  foldr
    (\decl acc ->
       Coq.App <$>
       withBoundVar (Imp.TypedVar (Imp.funName decl) (Imp.funDeclTy decl)) acc <*>
       (transformDecl decl))
    (transformDecl (NonEmpty.last decls))
    (NonEmpty.init decls)


transformAssgnLoc :: Imp.VarId -> TransformM Imp.TypedVar
transformAssgnLoc id = do
  expr <- asks (Map.lookup id)
  case expr of
    Nothing -> throwError (UnknownVariable id)
    Just (_, ty) -> pure (Imp.TypedVar id ty)

collectAssgns :: [Imp.Stmt] -> TransformM (Set Imp.TypedVar)
collectAssgns = fmap mconcat . mapM collectAssgns'
  where
   collectAssgns' (Imp.Assgn loc _) = Set.singleton <$> transformAssgnLoc loc
   collectAssgns' _ = pure (Set.empty)

toTuple :: [Imp.TypedVar] -> Imp.Expr
toTuple vars =
  case map (Imp.VarRef . Imp.varName) vars of
    [] -> Imp.Unit
    [var] -> var
    vars' -> foldr1 Imp.Pair vars'

refAsTuple :: [Imp.TypedVar] -> VarContext
refAsTuple vars =
  case vars of
    [] -> Map.empty
    [Imp.TypedVar id ty] -> Map.singleton id (tupleRef, ty)
    vars' ->
      let (last':init') =
            (reverse . take (length vars') . iterate Coq.Snd) tupleRef
          refs = reverse (last' : map Coq.Fst init')
      in Map.fromList
           (zipWith (\(Imp.TypedVar id ty) ref -> (id, (ref, ty))) vars' refs)
  where
    tupleRef = Coq.Var (Coq.VarId 0)

tupleType :: [Imp.Ty] -> Coq.Ty
tupleType vars =
  case vars of
    [] -> Coq.TyUnit
    [ty] -> transformTy ty
    tys -> foldr1 Coq.TyProd (map transformTy tys)

varsAsTuple :: [Imp.TypedVar] -> TransformM (Coq.Expr Coq.VarId)
varsAsTuple vars =
  case map Imp.varName vars of
    [] -> pure Coq.Unit
    [var] -> varRef var
    vars' -> foldr1 Coq.Pair <$> (mapM varRef vars')

withVarsAsTuple :: [Imp.TypedVar]
                -> TransformM (Coq.Expr Coq.VarId)
                -> TransformM (Coq.Expr Coq.VarId)
withVarsAsTuple vars =
  local (Map.union (refAsTuple vars) . Map.map (first Coq.shiftVars)) .
  fmap (Coq.Abs (tupleType (map Imp.varType vars)))

transformStmts :: [Imp.Stmt] -> TransformM (Coq.Expr Coq.VarId)
transformStmts [] = throwError MissingReturnStmt
transformStmts (Imp.Return e:_) = transformExpr e
transformStmts (Imp.Assgn loc val:stmts) = do
  loc' <- transformAssgnLoc loc
  Coq.App <$> withBoundVar loc' (transformStmts stmts) <*> transformExpr val
transformStmts (Imp.VarDecl tyVar val:stmts) =
  Coq.App <$> withBoundVar tyVar (transformStmts stmts) <*> transformExpr val
transformStmts (Imp.If cond ifTrue ifFalse:stmts) = do
  assignments <- Set.toList <$> (
    Set.union <$> collectAssgns ifTrue <*> collectAssgns (fromMaybe [] ifFalse))
  let retModified = Imp.Return (toTuple assignments)
      ifTrue' = ifTrue ++ [retModified]
      ifFalse' = fromMaybe [] ifFalse ++ [retModified]
  Coq.App <$> withVarsAsTuple assignments (transformStmts stmts) <*>
    (Coq.If <$> transformExpr cond <*> transformStmts ifTrue' <*>
     transformStmts ifFalse')
transformStmts (Imp.While cond body:stmts) = do
  assignments <- Set.toList <$> (collectAssgns body)
  let retModified = Imp.Return (Imp.Inr (toTuple assignments))
      body' = body ++ [retModified]
  coqInit <- varsAsTuple assignments
  coqBody <-
    withVarsAsTuple
      assignments
      (Coq.If <$> transformExpr cond <*> transformStmts body' <*>
       pure (Coq.Inl Coq.Unit))
  stmts' <- withVarsAsTuple assignments (transformStmts stmts)
  pure (Coq.App stmts' (Coq.Iter coqBody coqInit))

transformExpr :: Imp.Expr -> TransformM (Coq.Expr Coq.VarId)
transformExpr (Imp.VarRef id) = varRef id
transformExpr (Imp.IntLit i) = pure (Coq.IntLit i)
transformExpr (Imp.IntBinop op arg1 arg2) =
  Coq.IntBinop op <$> transformExpr arg1 <*> transformExpr arg2
transformExpr (Imp.IntComp comp arg1 arg2) =
  Coq.IntComp comp <$> transformExpr arg1 <*> transformExpr arg2
transformExpr (Imp.Pair x y) =
  Coq.Pair <$> transformExpr x <*> transformExpr y
transformExpr (Imp.Inl x) = Coq.Inl <$> transformExpr x
transformExpr (Imp.Inr x) = Coq.Inr <$> transformExpr x
transformExpr (Imp.Set arr index val) =
  Coq.Set <$> transformExpr arr <*> transformExpr index <*> transformExpr val
transformExpr (Imp.SetAtKey arr key val) =
  Coq.SetAtKey <$> transformExpr arr <*> transformExpr key <*>
  transformExpr val
transformExpr (Imp.Read arr index) =
  Coq.Read <$> transformExpr arr <*> transformExpr index
transformExpr (Imp.ReadAtKey arr key) =
  Coq.ReadAtKey <$> transformExpr arr <*> transformExpr key
transformExpr Imp.Unit = pure Coq.Unit
transformExpr (Imp.Call (Imp.VarRef "reduceByKey") args) =
  case args of
    [reducer, init, xs] -> do
      xs' <- transformExpr xs
      case reducer of
        Imp.Lambda [varA@(Imp.TypedVar _ tyVal), varB@(Imp.TypedVar _ tyVal')] body ->
          assert (tyVal == tyVal') $ do
            let tyVal' = transformTy tyVal
            let keyTy = Coq.TyInt -- TODO figure out the correct type
            let mapArgTy = Coq.TyProd keyTy (Coq.TyArr tyVal')
            mapper <-
              withAnonBoundVar mapArgTy $ do
                reducer' <- withBoundVarProd (varA, varB) (transformExpr body)
                init' <- transformExpr init
                pure
                  (Coq.Pair
                     (Coq.Fst (Coq.Var (Coq.VarId 0)))
                     (Coq.Fold reducer' init' (Coq.Snd (Coq.Var (Coq.VarId 0)))))
            pure (Coq.Map mapper (Coq.Group xs'))
    _ -> throwError (ExpectedArgs "reduceByKey" 3 (length args))
transformExpr (Imp.Call (Imp.VarRef "map") args) =
  case args of
    [mapper, xs] -> do
      xs' <- transformExpr xs
      case mapper of
        Imp.Lambda [var] body -> do
          mapper' <- withBoundVar var (transformExpr body)
          pure (Coq.Map mapper' xs')
    _ -> throwError (ExpectedArgs "map" 2 (length args))
transformExpr (Imp.Call (Imp.VarRef "flatMap") args) =
  case args of
    [mapper, xs] -> do
      xs' <- transformExpr xs
      case mapper of
        Imp.Lambda [var] body -> do
          mapper' <- withBoundVar var (transformExpr body)
          pure (Coq.Concat (Coq.Map mapper' xs'))
    _ -> throwError (ExpectedArgs "flatMap" 2 (length args))
transformExpr (Imp.Call fun args) =
  foldr
    (\arg f -> Coq.App <$> f <*> transformExpr arg)
    (transformExpr fun)
    args

transformTy :: Imp.Ty -> Coq.Ty
transformTy Imp.TyInt = Coq.TyInt
transformTy Imp.TyReal = Coq.TyReal
transformTy Imp.TyBool = Coq.TyBool
transformTy (Imp.TyArr ty) = Coq.TyArr (transformTy ty)
transformTy (Imp.TyFun args retTy) =
  foldr Coq.TyFun (transformTy retTy) (map transformTy args)
transformTy (Imp.TyProd a b) = Coq.TyProd (transformTy a) (transformTy b)
transformTy (Imp.TySum a b) = Coq.TySum (transformTy a) (transformTy b)
