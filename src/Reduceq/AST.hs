{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Reduceq.AST
  ( VarId(..)
  , Decl(..)
  , Ty(..)
  , TypedVar(..)
  , FunDecl(..)
  , Expr(..)
  , IntBinop(..)
  , Stmt(..)
  , IntComp(..)
  ) where

import Reduceq.Prelude

import Data.Data

newtype VarId = VarId Text deriving (Show, Eq, Ord, IsString)

data Decl = FunDecl !FunDecl deriving (Show, Eq, Ord)

data Ty
  = TyInt
  | TyReal
  | TyBool
  | TyArr !Ty
  deriving (Show, Eq, Ord)

data TypedVar = TypedVar
  { varName :: !VarId
  , varType :: !Ty
  } deriving (Show, Eq, Ord)

data FunDecl = FunctionDeclaration
  { funName :: !Text
  , funArguments :: [TypedVar]
  , funReturnType :: !Ty
  , funBody :: ![Stmt]
  } deriving (Show, Eq, Ord)

data IntBinop
  = IAdd
  | ISub
  | IMul
  deriving (Show, Eq, Ord, Data, Typeable)

data IntComp
  = IEq
  | ILt
  | IGt
  deriving (Show, Eq, Ord, Data, Typeable)

data Expr
  = IntBinop !IntBinop
             !Expr
             !Expr
  | IntComp !IntComp !Expr !Expr
  | VarRef !VarId
  | IntLit !Integer
  | Pair !Expr !Expr
  | Inl !Expr
  | Inr !Expr
  | Set !Expr !Expr !Expr -- Set array index val
  | Read !Expr !Expr -- Read array index
  | Unit
  deriving (Show, Eq, Ord)

data Stmt
  = Return !Expr
  | Assgn !VarId
          !Expr
  | VarDecl !TypedVar
            !Expr
  | If !Expr
       ![Stmt]
       !(Maybe [Stmt]) -- ^ optional else block
  | While !Expr
          ![Stmt]
  deriving (Show, Eq, Ord)
