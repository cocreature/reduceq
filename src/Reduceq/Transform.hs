{-# LANGUAGE OverloadedLists #-}
module Reduceq.Transform
  ( runTransformM
  , transformDecl
  , transformDecls
  , transformProgram
  , transformProgramSteps
  , TransformError(..)
  , showTransformError
  , TransformM
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

type VarContext = Map Imp.VarId (Expr', Imp.Ty)

data TransformError
  = UnknownVariable Imp.VarId
  | MissingReturnStmt
  | ExpectedArgs Imp.VarId
                 !Int
                 !Int
  | ExpectedLambda Imp.Expr
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
showTransformError (ExpectedLambda e) =
 "Expected lambda but got: " <> show e

newtype TransformM a =
  TransformM (ExceptT TransformError (Reader VarContext) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader VarContext
           , MonadError TransformError
           )

asNameHint :: Imp.VarId -> Maybe Text
asNameHint (Imp.VarId name) = Just name

ann :: e -> Coq.Ann () e
ann e = Coq.Ann () e

type Expr' = Coq.Ann () (Coq.Expr ())

withAnonVar :: Imp.TypedVar -> TransformM Expr' -> TransformM Expr'
withAnonVar (Imp.TypedVar name ty) =
  local
    (Map.insert
       name
       ( ann
           (ann (Coq.Var (Coq.VarId 0 (asNameHint name))) `Coq.Annotated`
            transformTy ty)
       , ty) .
     Map.map (first Coq.lift1))

-- | 'withBoundVar' behaves like 'withAnonVar' but also wraps the
-- expression in a lambda that binds the variable
withBoundVar :: Imp.TypedVar -> TransformM Expr' -> TransformM Expr'
withBoundVar var@(Imp.TypedVar name ty) =
  withAnonVar var . fmap (ann . Coq.Abs (transformTy ty) (Just name))

withAnonBoundVar :: Coq.Ty -> TransformM Expr' -> TransformM Expr'
withAnonBoundVar ty = local (Map.map (first Coq.lift1)) . fmap (ann . Coq.Abs ty Nothing)

withBoundVarProd :: (Imp.TypedVar, Imp.TypedVar) -> TransformM Expr' -> TransformM Expr'
withBoundVarProd (Imp.TypedVar fstName fstTy, Imp.TypedVar sndName sndTy) =
  assert (fstName /= sndName) $
  local
    (Map.insert
       fstName
       (ann (Coq.Fst (ann (Coq.Var (Coq.VarId 0 (asNameHint fstName))))), fstTy) .
     Map.insert
       sndName
       (ann (Coq.Snd (ann (Coq.Var (Coq.VarId 0 (asNameHint sndName))))), sndTy)) .
  fmap
    (ann . Coq.Abs (Coq.TyProd (transformTy fstTy) (transformTy sndTy)) Nothing)

varRef :: Imp.VarId -> TransformM Expr'
varRef id = do
  expr <- asks (Map.lookup id)
  case expr of
    Nothing -> throwError (UnknownVariable id)
    Just (e, _) -> pure e

runTransformM :: TransformM a -> Either TransformError a
runTransformM (TransformM a) = runReader (runExceptT a) Map.empty

transformDecl :: Imp.FunDecl -> TransformM Expr'
transformDecl (Imp.FunctionDeclaration (Imp.VarId name) args retTy body) =
  case body of
    Imp.ExternFunction
      -- TODO this needs to be lifted by the number of bound variables
     ->
      pure
        (ann
           (ann (Coq.ExternRef (Coq.ExternReference name coqTy)) `Coq.Annotated`
            coqTy))
    Imp.FunctionBody stmts ->
      (ann . (`Coq.Annotated` coqTy)) <$>
      foldr (.) identity (map withBoundVar args) (transformStmts stmts)
  where
    coqTy = transformTy (Imp.TyFun (map Imp.varType args) retTy)

transformDecls :: NonEmpty Imp.FunDecl -> TransformM Expr'
transformDecls decls
 -- declarations can only reference earlier declarations
 =
  foldr
    (\decl acc ->
       ann <$>
       (Coq.App <$>
        withBoundVar (Imp.TypedVar (Imp.funName decl) (Imp.funDeclTy decl)) acc <*>
        transformDecl decl))
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
      decls = Set.fromList (toListOf (traverse . cosmos . Imp._VarDecl . _1 . to Imp.varName) stmts)
      assgns' = assgns Set.\\ decls
  (fmap Set.fromList . traverse transformAssgnLoc . toList) assgns'

toTuple :: [Imp.TypedVar] -> Imp.Expr
toTuple vars =
  case map (Imp.VarRef . Imp.varName) vars of
    [] -> Imp.Unit
    [var] -> var
    vars' -> foldr1 Imp.Pair vars'

refAsTuple :: Expr' -> [Imp.TypedVar] -> VarContext
refAsTuple tupleRef vars =
  case vars of
    [] -> Map.empty
    [Imp.TypedVar id ty] -> Map.singleton id (tupleRef, ty)
    vars' ->
      let (last':init') =
            (reverse . take (length vars') . iterate (ann . Coq.Snd)) tupleRef
          refs = reverse (last' : map (ann . Coq.Fst) init')
      in Map.fromList
           (zipWith (\(Imp.TypedVar id ty) ref -> (id, (ref, ty))) vars' refs)

tupleType :: [Imp.Ty] -> Coq.Ty
tupleType vars =
  case vars of
    [] -> Coq.TyUnit
    [ty] -> transformTy ty
    tys -> foldr1 Coq.TyProd (map transformTy tys)

varsAsTuple :: [Imp.TypedVar] -> TransformM Expr'
varsAsTuple vars =
  case map Imp.varName vars of
    [] -> pure (ann Coq.Unit)
    [var] -> varRef var
    vars' -> foldr1 (\x y -> ann (Coq.Pair x y)) <$> (mapM varRef vars')

withVarsAsTuple :: [Imp.TypedVar] -> TransformM Expr' -> TransformM Expr'
withVarsAsTuple vars =
  local
    (Map.union (refAsTuple (ann (Coq.Var (Coq.VarId 0 nameHint))) vars) .
     Map.map (first Coq.lift1)) .
  fmap (ann . Coq.Abs (tupleType (map Imp.varType vars)) name)
  where
    (nameHint, name) =
      case vars of
        [Imp.TypedVar name' _] -> (asNameHint name', Just name')
        _ -> (Nothing, Nothing)

-- Used in folds. The first expression represents the name of the
-- bound array element.
withAccVarsAsTuple :: Imp.TypedVar -> [Imp.TypedVar] -> TransformM Expr' -> TransformM Expr'
withAccVarsAsTuple (Imp.TypedVar elName elTy) vars =
  local
    (Map.insert
       elName
       (ann (Coq.Snd (ann (Coq.Var (Coq.VarId 0 Nothing)))), elTy) .
     Map.union
       (refAsTuple (ann (Coq.Fst (ann (Coq.Var (Coq.VarId 0 Nothing))))) vars) .
     Map.map (first Coq.lift1)) .
  fmap
    (ann .
     Coq.Abs
       (Coq.TyProd (tupleType (map Imp.varType vars)) (transformTy elTy))
       Nothing)

transformStmts :: [Imp.Stmt] -> TransformM Expr'
transformStmts [] = throwError MissingReturnStmt
transformStmts (Imp.Return e:_) = transformExpr e
transformStmts (Imp.Assgn loc val:stmts) = do
  loc' <- transformAssgnLoc loc
  fmap ann $ Coq.App <$> withBoundVar loc' (transformStmts stmts) <*> transformExpr val
transformStmts (Imp.VarDecl tyVar@(Imp.TypedVar _ ty) val:stmts) =
  fmap ann $
  Coq.App <$> withBoundVar tyVar (transformStmts stmts) <*>
  ((ann . (`Coq.Annotated` transformTy ty)) <$> transformExpr val)
transformStmts (Imp.If cond ifTrue ifFalse:stmts) = do
  assignments <-
    Set.toList <$>
    (Set.union <$> collectAssgns ifTrue <*> collectAssgns (fromMaybe [] ifFalse))
  let retModified = Imp.Return (toTuple assignments)
      ifTrue' = ifTrue ++ [retModified]
      ifFalse' = fromMaybe [] ifFalse ++ [retModified]
  fmap ann $
    Coq.App <$> withVarsAsTuple assignments (transformStmts stmts) <*>
    (ann <$>
     (Coq.If <$> transformExpr cond <*> transformStmts ifTrue' <*>
      transformStmts ifFalse'))
transformStmts (Imp.Match x (Imp.MatchClause l ifL) (Imp.MatchClause r ifR):stmts) = do
  assignments <-
    Set.toList <$> (Set.union <$> collectAssgns ifL <*> collectAssgns ifR)
  let retModified = Imp.Return (toTuple assignments)
      ifL' = ifL ++ [retModified]
      ifR' = ifR ++ [retModified]
  fmap ann $
    Coq.App <$> withVarsAsTuple assignments (transformStmts stmts) <*>
    (ann <$>
     (Coq.Case <$> transformExpr x <*> withAnonVar l (transformStmts ifL') <*>
      withAnonVar r (transformStmts ifR')))
transformStmts (Imp.While cond body:stmts) = do
  assignments <- Set.toList <$> collectAssgns body
  let retModified = Imp.Return (Imp.Inr (toTuple assignments))
      body' = body ++ [retModified]
  coqInit <- varsAsTuple assignments
  coqBody <-
    withVarsAsTuple assignments . fmap ann $
    (Coq.If <$> transformExpr cond <*> transformStmts body' <*>
     pure (ann (Coq.Inl (ann Coq.Unit))))
  stmts' <- withVarsAsTuple assignments (transformStmts stmts)
  pure (ann (Coq.App stmts' (ann (Coq.Iter coqBody coqInit))))
transformStmts (Imp.ForEach var array body:stmts) = do
  assignments <- Set.toList <$> collectAssgns body
  let retModified = Imp.Return (toTuple assignments)
      body' = body ++ [retModified]
  coqArray <- transformExpr array
  coqBody <- withAccVarsAsTuple var assignments (transformStmts body')
  coqInit <- varsAsTuple assignments
  stmts' <- withVarsAsTuple assignments (transformStmts stmts)
  pure (ann (Coq.App stmts' (ann (Coq.Fold coqBody coqInit coqArray))))

transformExpr :: Imp.Expr -> TransformM (Coq.Ann () (Coq.Expr ()))
transformExpr (Imp.VarRef id) = varRef id
transformExpr (Imp.IntLit i) = pure (ann (Coq.IntLit i))
transformExpr (Imp.IntBinop op arg1 arg2) =
  fmap ann $ Coq.IntBinop op <$> transformExpr arg1 <*> transformExpr arg2
transformExpr (Imp.IntComp comp arg1 arg2) =
  fmap ann $ Coq.IntComp comp <$> transformExpr arg1 <*> transformExpr arg2
transformExpr (Imp.Pair x y) =
  fmap ann $ Coq.Pair <$> transformExpr x <*> transformExpr y
transformExpr (Imp.Fst x) = ann . Coq.Fst <$> transformExpr x
transformExpr (Imp.Snd x) = ann . Coq.Snd <$> transformExpr x
transformExpr (Imp.Inl x) = ann . Coq.Inl <$> transformExpr x
transformExpr (Imp.Inr x) = ann . Coq.Inr <$> transformExpr x
transformExpr (Imp.Set arr index val) =
  fmap ann $ Coq.Set <$> transformExpr arr <*> transformExpr index <*> transformExpr val
transformExpr (Imp.SetAtKey arr key val) =
  fmap ann $ Coq.SetAtKey <$> transformExpr arr <*> transformExpr key <*>
  transformExpr val
transformExpr (Imp.Read arr index) =
  fmap ann $ Coq.Read <$> transformExpr arr <*> transformExpr index
transformExpr (Imp.ReadAtKey arr key) =
  fmap ann $ Coq.ReadAtKey <$> transformExpr arr <*> transformExpr key
transformExpr Imp.Unit = pure (ann Coq.Unit)
transformExpr (Imp.Call (Imp.VarRef "reduceByKey") args) =
  case args of
    [reducer, init, xs] -> do
      xs' <- transformExpr xs
      case reducer of
        Imp.Lambda [varA@(Imp.TypedVar name tyVal), varB@(Imp.TypedVar _ tyVal')] body ->
          assert (tyVal == tyVal') $ do
            let tyVal'' = transformTy tyVal
            let keyTy = Coq.TyInt -- TODO figure out the correct type
            let mapArgTy = Coq.TyProd keyTy (Coq.TyArr tyVal'')
            mapper <-
              withAnonBoundVar mapArgTy $ do
                reducer' <- withBoundVarProd (varA, varB) (transformExpr body)
                init' <- transformExpr init
                (pure . ann)
                  (Coq.Pair
                     (ann (Coq.Fst (ann (Coq.Var (Coq.VarId 0 (asNameHint name))))))
                     (ann (Coq.Fold
-- We are moving this below the binder passed to map so we need to
-- lift by 1 except for the variable bound in the map itself.
                        (Coq.liftVarsAbove 1 1 reducer')
                        init'
                        (ann (Coq.Snd (ann (Coq.Var (Coq.VarId 0 (Just "reducer")))))))))
            pure (ann (Coq.Map mapper (ann (Coq.Group xs'))))
        _ -> throwError (ExpectedLambda reducer)
    _ -> throwError (ExpectedArgs "reduceByKey" 3 (length args))
transformExpr (Imp.Call (Imp.VarRef "map") args) =
  case args of
    [mapper, xs] -> do
      xs' <- transformExpr xs
      case mapper of
        Imp.Lambda [var] body -> do
          mapper' <- withBoundVar var (transformExpr body)
          pure (ann (Coq.Map mapper' xs'))
        _ -> throwError (ExpectedLambda mapper)
    _ -> throwError (ExpectedArgs "map" 2 (length args))
transformExpr (Imp.Call (Imp.VarRef "flatMap") args) =
  case args of
    [mapper, xs] -> do
      xs' <- transformExpr xs
      case mapper of
        Imp.Lambda [var] body -> do
          mapper' <- withBoundVar var (transformExpr body)
          pure (ann (Coq.Concat (ann (Coq.Map mapper' xs'))))
        _ -> throwError (ExpectedLambda mapper)
    _ -> throwError (ExpectedArgs "flatMap" 2 (length args))
transformExpr (Imp.Call (Imp.VarRef "length") args) =
  case args of
    [xs] -> ann . Coq.Length <$> transformExpr xs
    _ -> throwError (ExpectedArgs "length" 1 (length args))
transformExpr (Imp.Call (Imp.VarRef "range") args) =
  case args of
    [initial, final, step] ->
      fmap ann $
      Coq.Range <$> transformExpr initial <*> transformExpr final <*>
      transformExpr step
    _ -> throwError (ExpectedArgs "range" 3 (length args))
transformExpr (Imp.Call (Imp.VarRef "replicate") args) =
  case args of
    [count, val] ->
      fmap ann $ Coq.Replicate <$> transformExpr count <*> transformExpr val
    _ -> throwError (ExpectedArgs "replicate" 2 (length args))
transformExpr (Imp.Call (Imp.VarRef "zip") args) =
  case args of
    [xs, ys] ->
      fmap ann $ Coq.Zip <$> transformExpr xs <*> transformExpr ys
    _ -> throwError (ExpectedArgs "zip" 2 (length args))
transformExpr (Imp.Call (Imp.VarRef "fold") args) =
  case args of
    [f, i, xs] ->
      fmap ann $
      Coq.Fold <$> transformExpr f <*> transformExpr i <*> transformExpr xs
    _ -> throwError (ExpectedArgs "fold" 3 (length args))
transformExpr (Imp.Call (Imp.VarRef "write") args) =
  case args of
    [xs, i, val] ->
      fmap ann $
      Coq.Set <$> transformExpr xs <*> transformExpr i <*> transformExpr val
    _ -> throwError (ExpectedArgs "write" 3 (length args))
transformExpr (Imp.Call (Imp.VarRef "concat") args) =
  case args of
    [xs] ->
      fmap ann $ Coq.Concat <$> transformExpr xs
    _ -> throwError (ExpectedArgs "concat" 1 (length args))
transformExpr (Imp.Call fun args) =
  foldl'
    (\f arg -> fmap ann $ Coq.App <$> f <*> transformExpr arg)
    (transformExpr fun)
    args
transformExpr Imp.EmptyArray = pure (ann (Coq.List []))
transformExpr (Imp.Lambda vars body) =
  foldr (\var acc -> withBoundVar var acc) (transformExpr body) vars

transformTy :: Imp.Ty -> Coq.Ty
transformTy Imp.TyInt = Coq.TyInt
transformTy Imp.TyReal = Coq.TyReal
transformTy Imp.TyBool = Coq.TyBool
transformTy (Imp.TyArr ty) = Coq.TyArr (transformTy ty)
transformTy (Imp.TyFun args retTy) =
  foldr Coq.TyFun (transformTy retTy) (map transformTy args)
transformTy (Imp.TyProd a b) = Coq.TyProd (transformTy a) (transformTy b)
transformTy (Imp.TySum a b) = Coq.TySum (transformTy a) (transformTy b)
transformTy Imp.TyUnit = Coq.TyUnit

transformProgram :: Imp.Program -> TransformM Expr'
transformProgram (Imp.Program decls) = transformDecls decls

transformProgramSteps :: Imp.ProgramSteps Imp.Program -> TransformM (Imp.ProgramSteps (Coq.Expr ()))
transformProgramSteps (Imp.ProgramSteps initial steps final) =
  fmap (fmap Coq.stripAnn) $
  Imp.ProgramSteps <$> transformProgram initial <*>
  traverse transformProgram steps <*>
  transformProgram final
