{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Reduceq.Transform
  ( runTransformM
  , transformDecl
  ) where

import           Reduceq.Prelude

import           Data.Map (Map)
import qualified Data.Map as Map
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

transformStmts :: [AST.Stmt] -> TransformM CoqAST.Expr
transformStmts [] = panic "Missing return statement"
transformStmts (AST.Return e : _) = transformExpr e

transformExpr :: AST.Expr -> TransformM CoqAST.Expr
transformExpr (AST.VarRef id) = varRef id

transformTy :: AST.Ty -> CoqAST.Ty
transformTy AST.TyInt = CoqAST.TyInt
