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

type VarContext = Map AST.VarId CoqAST.Expr

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
    (Map.insert name (CoqAST.Var $ CoqAST.VarId 0) . Map.map CoqAST.shiftVars) .
  fmap (CoqAST.Abs (transformTy ty))

varRef :: AST.VarId -> TransformM CoqAST.Expr
varRef id = do
  expr <- asks (Map.lookup id)
  case expr of
    Nothing -> panic ("Unknown variable identifier: " <> show id)
    Just e -> pure e

runTransformM :: TransformM a -> a
runTransformM (TransformM a) = runReader a Map.empty

transformDecl :: AST.FunDecl -> TransformM CoqAST.Expr
transformDecl (AST.FunctionDeclaration _ args _ body) =
  foldr (.) identity (map withBoundVar args) (transformStmts body)

transformLoc :: AST.AssgnLocation -> TransformM AST.TypedVar
-- TODO figure out the correct type instead of defaulting to TyInt
transformLoc (AST.VarLoc id) = return (AST.TypedVar id AST.TyInt)

collectAssgns :: [AST.Stmt] -> TransformM (Set AST.TypedVar)
collectAssgns = fmap mconcat . mapM collectAssgns'
  where
   collectAssgns' (AST.Assgn loc _) = Set.singleton <$> transformLoc loc
   collectAssgns' _ = pure (Set.empty)

toTuple :: [AST.TypedVar] -> AST.Expr
toTuple vars =
  case map (AST.VarRef . AST.varName) vars of
    [] -> AST.Unit
    [var] -> var
    vars' -> foldr1 AST.Pair vars'

refAsTuple :: [AST.VarId] -> Map AST.VarId CoqAST.Expr
refAsTuple vars =
  case vars of
    [] -> Map.empty
    [var] -> Map.singleton var tupleRef
    vars' ->
      let (last':init') =
            (reverse . take (length vars') . iterate CoqAST.Snd) tupleRef
          refs = reverse (last' : map CoqAST.Fst init')
      in Map.fromList (zip vars' refs)
  where
    tupleRef = CoqAST.Var (CoqAST.VarId 0)

tupleType :: [AST.Ty] -> CoqAST.Ty
tupleType vars =
  case vars of
    [] -> CoqAST.TyUnit
    [ty] -> transformTy ty
    tys -> foldr1 CoqAST.TyProd (map transformTy tys)

withVarsAsTuple :: [AST.TypedVar]
                -> TransformM CoqAST.Expr
                -> TransformM CoqAST.Expr
withVarsAsTuple vars = local (Map.union (refAsTuple (map AST.varName vars))). fmap (CoqAST.Abs (tupleType (map AST.varType vars)))

transformStmts :: [AST.Stmt] -> TransformM CoqAST.Expr
transformStmts [] = panic "Missing return statement"
transformStmts (AST.Return e:_) = transformExpr e
transformStmts (AST.Assgn loc val:stmts) = do
  loc' <- transformLoc loc
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

transformExpr :: AST.Expr -> TransformM CoqAST.Expr
transformExpr (AST.VarRef id) = varRef id
transformExpr (AST.IntLit i) = pure (CoqAST.IntLit i)
transformExpr (AST.IntBinop op arg1 arg2) =
  CoqAST.IntBinop op <$> transformExpr arg1 <*> transformExpr arg2
transformExpr (AST.IntComp comp arg1 arg2) =
  CoqAST.IntComp comp <$> transformExpr arg1 <*> transformExpr arg2
transformExpr (AST.Pair x y) =
  CoqAST.Pair <$> transformExpr x <*> transformExpr y

transformTy :: AST.Ty -> CoqAST.Ty
transformTy AST.TyInt = CoqAST.TyInt
