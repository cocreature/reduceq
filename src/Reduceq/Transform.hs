{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Reduceq.Transform
  ( runTransformM
  , transformDecl
  ) where

import           Reduceq.Prelude

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Reduceq.AST as AST
import qualified Reduceq.CoqAST as CoqAST

type VarContext = Map AST.VarId (CoqAST.Expr, AST.Ty)

newtype TransformM a =
  TransformM (Reader VarContext a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader VarContext
           )

withBoundVar :: AST.TypedVar -> TransformM CoqAST.Expr -> TransformM CoqAST.Expr
withBoundVar (AST.TypedVar name ty) =
  local
    (Map.insert name (CoqAST.Var $ CoqAST.VarId 0, ty) .
     Map.map (first CoqAST.shiftVars)) .
  fmap (CoqAST.Abs (transformTy ty))

varRef :: AST.VarId -> TransformM CoqAST.Expr
varRef id = do
  expr <- asks (Map.lookup id)
  case expr of
    Nothing -> panic ("Unknown variable identifier: " <> show id)
    Just (e, _) -> pure e

runTransformM :: TransformM a -> a
runTransformM (TransformM a) = runReader a Map.empty

transformDecl :: AST.FunDecl -> TransformM CoqAST.Expr
transformDecl (AST.FunctionDeclaration _ args _ body) =
  foldr (.) identity (map withBoundVar args) (transformStmts body)

transformAssgnLoc :: AST.VarId -> TransformM AST.TypedVar
transformAssgnLoc id = do
  expr <- asks (Map.lookup id)
  case expr of
    Nothing -> panic ("Unknown variable identifier: " <> show id)
    Just (_, ty) -> pure (AST.TypedVar id ty)

collectAssgns :: [AST.Stmt] -> TransformM (Set AST.TypedVar)
collectAssgns = fmap mconcat . mapM collectAssgns'
  where
   collectAssgns' (AST.Assgn loc _) = Set.singleton <$> transformAssgnLoc loc
   collectAssgns' _ = pure (Set.empty)

toTuple :: [AST.TypedVar] -> AST.Expr
toTuple vars =
  case map (AST.VarRef . AST.varName) vars of
    [] -> AST.Unit
    [var] -> var
    vars' -> foldr1 AST.Pair vars'

refAsTuple :: [AST.TypedVar] -> VarContext
refAsTuple vars =
  case vars of
    [] -> Map.empty
    [AST.TypedVar id ty] -> Map.singleton id (tupleRef, ty)
    vars' ->
      let (last':init') =
            (reverse . take (length vars') . iterate CoqAST.Snd) tupleRef
          refs = reverse (last' : map CoqAST.Fst init')
      in Map.fromList
           (zipWith (\(AST.TypedVar id ty) ref -> (id, (ref, ty))) vars' refs)
  where
    tupleRef = CoqAST.Var (CoqAST.VarId 0)

tupleType :: [AST.Ty] -> CoqAST.Ty
tupleType vars =
  case vars of
    [] -> CoqAST.TyUnit
    [ty] -> transformTy ty
    tys -> foldr1 CoqAST.TyProd (map transformTy tys)

varsAsTuple :: [AST.TypedVar] -> TransformM CoqAST.Expr
varsAsTuple vars =
  case map AST.varName vars of
    [] -> pure CoqAST.Unit
    [var] -> varRef var
    vars' -> foldr1 CoqAST.Pair <$> (mapM varRef vars')

withVarsAsTuple :: [AST.TypedVar]
                -> TransformM CoqAST.Expr
                -> TransformM CoqAST.Expr
withVarsAsTuple vars =
  local (Map.union (refAsTuple vars) . Map.map (first CoqAST.shiftVars)) .
  fmap (CoqAST.Abs (tupleType (map AST.varType vars)))

transformStmts :: [AST.Stmt] -> TransformM CoqAST.Expr
transformStmts [] = panic "Missing return statement"
transformStmts (AST.Return e:_) = transformExpr e
transformStmts (AST.Assgn loc val:stmts) = do
  loc' <- transformAssgnLoc loc
  CoqAST.App <$> withBoundVar loc' (transformStmts stmts) <*> transformExpr val
transformStmts (AST.VarDecl tyVar val:stmts) =
  CoqAST.App <$> withBoundVar tyVar (transformStmts stmts) <*> transformExpr val
transformStmts (AST.If cond ifTrue ifFalse:stmts) = do
  assignments <- Set.toList <$> (
    Set.union <$> collectAssgns ifTrue <*> collectAssgns (fromMaybe [] ifFalse))
  let retModified = AST.Return (toTuple assignments)
      ifTrue' = ifTrue ++ [retModified]
      ifFalse' = fromMaybe [] ifFalse ++ [retModified]
  CoqAST.App <$> withVarsAsTuple assignments (transformStmts stmts) <*>
    (CoqAST.If <$> transformExpr cond <*> transformStmts ifTrue' <*>
     transformStmts ifFalse')
transformStmts (AST.While cond body:stmts) = do
  assignments <- Set.toList <$> (collectAssgns body)
  let retModified = AST.Return (AST.Inr (toTuple assignments))
      body' = body ++ [retModified]
  coqInit <- varsAsTuple assignments
  coqBody <-
    withVarsAsTuple
      assignments
      (CoqAST.If <$> transformExpr cond <*> transformStmts body' <*>
       pure (CoqAST.Inl CoqAST.Unit))
  stmts' <- withVarsAsTuple assignments (transformStmts stmts)
  pure (CoqAST.App stmts' (CoqAST.Iter coqBody coqInit))

transformExpr :: AST.Expr -> TransformM CoqAST.Expr
transformExpr (AST.VarRef id) = varRef id
transformExpr (AST.IntLit i) = pure (CoqAST.IntLit i)
transformExpr (AST.IntBinop op arg1 arg2) =
  CoqAST.IntBinop op <$> transformExpr arg1 <*> transformExpr arg2
transformExpr (AST.IntComp comp arg1 arg2) =
  CoqAST.IntComp comp <$> transformExpr arg1 <*> transformExpr arg2
transformExpr (AST.Pair x y) =
  CoqAST.Pair <$> transformExpr x <*> transformExpr y
transformExpr (AST.Inl x) = CoqAST.Inl <$> transformExpr x
transformExpr (AST.Inr x) = CoqAST.Inr <$> transformExpr x
transformExpr (AST.Set arr index val) =
  CoqAST.Set <$> transformExpr arr <*> transformExpr index <*> transformExpr val
transformExpr (AST.Read arr index) =
  CoqAST.Read <$> transformExpr arr <*> transformExpr index
transformExpr AST.Unit = pure CoqAST.Unit

transformTy :: AST.Ty -> CoqAST.Ty
transformTy AST.TyInt = CoqAST.TyInt
transformTy (AST.TyArr ty) = CoqAST.TyArr (transformTy ty)
