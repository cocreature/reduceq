{-# LANGUAGE OverloadedLists #-}
module Reduceq.Transform
  ( runTransformM
  , transformDecl
  , transformDecls
  , transformProgram
  , transformProgramSteps
  , TransformError(..)
  , showTransformError
  ) where

import           Reduceq.Prelude

import           Control.Lens hiding (index, op)
import qualified Data.List.NonEmpty as NonEmpty
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set

import qualified Reduceq.Coq as Coq
import qualified Reduceq.Imp as Imp

type VarContext = Map Imp.VarId (Coq.Expr, Imp.Ty)

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

withAnonVar :: Imp.TypedVar -> TransformM Coq.Expr -> TransformM Coq.Expr
withAnonVar (Imp.TypedVar name ty) =
  local
    (Map.insert name (Coq.Var (Coq.VarId 0), ty) . Map.map (first Coq.shiftVars))

-- | 'withBoundVar' behaves like 'withAnonVar' but also wraps the
-- expression in a lambda that binds the variable
withBoundVar :: Imp.TypedVar -> TransformM Coq.Expr -> TransformM Coq.Expr
withBoundVar var@(Imp.TypedVar _name ty) =
  withAnonVar var . fmap (Coq.Abs (transformTy ty))

withAnonBoundVar :: Coq.Ty -> TransformM Coq.Expr -> TransformM Coq.Expr
withAnonBoundVar ty = local (Map.map (first Coq.shiftVars)) . fmap (Coq.Abs ty)

withBoundVarProd :: (Imp.TypedVar, Imp.TypedVar) -> TransformM Coq.Expr -> TransformM Coq.Expr
withBoundVarProd (Imp.TypedVar fstName fstTy, Imp.TypedVar sndName sndTy) =
  assert (fstName /= sndName) $
  local
    (Map.insert fstName (Coq.Fst (Coq.Var (Coq.VarId 0)), fstTy) .
     Map.insert sndName (Coq.Snd (Coq.Var (Coq.VarId 0)), sndTy)) .
  fmap (Coq.Abs (Coq.TyProd (transformTy fstTy) (transformTy sndTy)))

varRef :: Imp.VarId -> TransformM Coq.Expr
varRef id = do
  expr <- asks (Map.lookup id)
  case expr of
    Nothing -> throwError (UnknownVariable id)
    Just (e, _) -> pure e

runTransformM :: TransformM a -> Either TransformError a
runTransformM (TransformM a) = runReader (runExceptT a) Map.empty

transformDecl :: Imp.FunDecl -> TransformM Coq.Expr
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

transformDecls :: NonEmpty Imp.FunDecl -> TransformM Coq.Expr
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
collectAssgns stmts = do
  -- Scoping is quite primitive. If a variable is declared anywhere in
  -- a block (i.e., the list of statements) it hides any references to
  -- variables outside of the block so we don’t include it in the list
  -- of external assignments.
  let assgns = Set.fromList (toListOf (traverse . Imp.collectAssgnLocs) stmts)
      decls = Set.fromList (toListOf (traverse . Imp._VarDecl . _1 . to Imp.varName) stmts)
      assgns' = assgns Set.\\ decls
  (fmap Set.fromList . traverse transformAssgnLoc . toList) assgns'

toTuple :: [Imp.TypedVar] -> Imp.Expr
toTuple vars =
  case map (Imp.VarRef . Imp.varName) vars of
    [] -> Imp.Unit
    [var] -> var
    vars' -> foldr1 Imp.Pair vars'

refAsTuple :: Coq.Expr -> [Imp.TypedVar] -> VarContext
refAsTuple tupleRef vars =
  case vars of
    [] -> Map.empty
    [Imp.TypedVar id ty] -> Map.singleton id (tupleRef, ty)
    vars' ->
      let (last':init') =
            (reverse . take (length vars') . iterate Coq.Snd) tupleRef
          refs = reverse (last' : map Coq.Fst init')
      in Map.fromList
           (zipWith (\(Imp.TypedVar id ty) ref -> (id, (ref, ty))) vars' refs)

tupleType :: [Imp.Ty] -> Coq.Ty
tupleType vars =
  case vars of
    [] -> Coq.TyUnit
    [ty] -> transformTy ty
    tys -> foldr1 Coq.TyProd (map transformTy tys)

varsAsTuple :: [Imp.TypedVar] -> TransformM Coq.Expr
varsAsTuple vars =
  case map Imp.varName vars of
    [] -> pure Coq.Unit
    [var] -> varRef var
    vars' -> foldr1 Coq.Pair <$> (mapM varRef vars')

withVarsAsTuple :: [Imp.TypedVar]
                -> TransformM Coq.Expr
                -> TransformM Coq.Expr
withVarsAsTuple vars =
  local (Map.union (refAsTuple (Coq.Var (Coq.VarId 0)) vars) . Map.map (first Coq.shiftVars)) .
  fmap (Coq.Abs (tupleType (map Imp.varType vars)))

-- Used in folds. The first expression represents the name of the
-- bound array element.
withAccVarsAsTuple :: Imp.TypedVar -> [Imp.TypedVar] -> TransformM Coq.Expr -> TransformM Coq.Expr
withAccVarsAsTuple (Imp.TypedVar elName elTy) vars =
  local
    (Map.insert elName (Coq.Snd (Coq.Var (Coq.VarId 0)), elTy) .
     Map.union (refAsTuple (Coq.Fst (Coq.Var (Coq.VarId 0))) vars) .
     Map.map (first Coq.shiftVars)) .
  fmap
    (Coq.Abs (Coq.TyProd (tupleType (map Imp.varType vars)) (transformTy elTy)))

transformStmts :: [Imp.Stmt] -> TransformM Coq.Expr
transformStmts [] = throwError MissingReturnStmt
transformStmts (Imp.Return e:_) = transformExpr e
transformStmts (Imp.Assgn loc val:stmts) = do
  loc' <- transformAssgnLoc loc
  Coq.App <$> withBoundVar loc' (transformStmts stmts) <*> transformExpr val
transformStmts (Imp.VarDecl tyVar@(Imp.TypedVar _ ty) val:stmts) =
  Coq.App <$> withBoundVar tyVar (transformStmts stmts) <*>
  ((`Coq.Annotated` transformTy ty) <$> transformExpr val)
transformStmts (Imp.If cond ifTrue ifFalse:stmts) = do
  assignments <- Set.toList <$> (
    Set.union <$> collectAssgns ifTrue <*> collectAssgns (fromMaybe [] ifFalse))
  let retModified = Imp.Return (toTuple assignments)
      ifTrue' = ifTrue ++ [retModified]
      ifFalse' = fromMaybe [] ifFalse ++ [retModified]
  Coq.App <$> withVarsAsTuple assignments (transformStmts stmts) <*>
    (Coq.If <$> transformExpr cond <*> transformStmts ifTrue' <*>
     transformStmts ifFalse')
transformStmts (Imp.Match x (Imp.MatchClause l ifL) (Imp.MatchClause r ifR):stmts) = do
  assignments <-
    Set.toList <$> (Set.union <$> collectAssgns ifL <*> collectAssgns ifR)
  let retModified = Imp.Return (toTuple assignments)
      ifL' = ifL ++ [retModified]
      ifR' = ifR ++ [retModified]
  Coq.App <$> withVarsAsTuple assignments (transformStmts stmts) <*>
    (Coq.Case <$> transformExpr x <*> withAnonVar l (transformStmts ifL') <*>
     withAnonVar r (transformStmts ifR'))
transformStmts (Imp.While cond body:stmts) = do
  assignments <- Set.toList <$> collectAssgns body
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
transformStmts (Imp.ForEach var array body:stmts) = do
  assignments <- Set.toList <$> collectAssgns body
  let retModified = Imp.Return (toTuple assignments)
      body' = body ++ [retModified]
  coqArray <- transformExpr array
  coqBody <- withAccVarsAsTuple var assignments (transformStmts body')
  coqInit <- varsAsTuple assignments
  stmts' <- withVarsAsTuple assignments (transformStmts stmts)
  pure (Coq.App stmts' (Coq.Fold coqBody coqInit coqArray))

transformExpr :: Imp.Expr -> TransformM Coq.Expr
transformExpr (Imp.VarRef id) = varRef id
transformExpr (Imp.IntLit i) = pure (Coq.IntLit i)
transformExpr (Imp.IntBinop op arg1 arg2) =
  Coq.IntBinop op <$> transformExpr arg1 <*> transformExpr arg2
transformExpr (Imp.IntComp comp arg1 arg2) =
  Coq.IntComp comp <$> transformExpr arg1 <*> transformExpr arg2
transformExpr (Imp.Pair x y) =
  Coq.Pair <$> transformExpr x <*> transformExpr y
transformExpr (Imp.Fst x) = Coq.Fst <$> transformExpr x
transformExpr (Imp.Snd x) = Coq.Snd <$> transformExpr x
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
            let tyVal'' = transformTy tyVal
            let keyTy = Coq.TyInt -- TODO figure out the correct type
            let mapArgTy = Coq.TyProd keyTy (Coq.TyArr tyVal'')
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
transformExpr Imp.EmptyArray = pure (Coq.List [])

transformTy :: Imp.Ty -> Coq.Ty
transformTy Imp.TyInt = Coq.TyInt
transformTy Imp.TyReal = Coq.TyReal
transformTy Imp.TyBool = Coq.TyBool
transformTy (Imp.TyArr ty) = Coq.TyArr (transformTy ty)
transformTy (Imp.TyFun args retTy) =
  foldr Coq.TyFun (transformTy retTy) (map transformTy args)
transformTy (Imp.TyProd a b) = Coq.TyProd (transformTy a) (transformTy b)
transformTy (Imp.TySum a b) = Coq.TySum (transformTy a) (transformTy b)

transformProgram :: Imp.Program -> TransformM Coq.Expr
transformProgram (Imp.Program decls) = transformDecls decls

transformProgramSteps :: Imp.ProgramSteps Imp.Program -> TransformM (Imp.ProgramSteps Coq.Expr)
transformProgramSteps (Imp.ProgramSteps initial steps final) =
  Imp.ProgramSteps <$> transformProgram initial <*>
  traverse transformProgram steps <*>
  transformProgram final
