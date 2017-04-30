{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Reduceq.AST
  ( VarId
  , mkVarId
  , Decl(..)
  , Ty(..)
  , TypedVar(..)
  , FunDecl(..)
  , Expr(..)
  , IntBinop(..)
  , Stmt(..)
  , AssgnLocation(..)
  , IntComp(..)
  ) where

import Reduceq.Prelude

newtype VarId = VarId Text deriving (Show, Eq, Ord, IsString)

mkVarId :: Text -> VarId
mkVarId = VarId

data Decl = FunDecl !FunDecl deriving (Show, Eq, Ord)

data Ty
  = TyInt
  | TyReal
  | TyBool
  | TyList !Ty
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
  deriving (Show, Eq, Ord)

data IntComp
  = IEq
  | ILt
  | IGt
  deriving (Show, Eq, Ord)

data Expr
  = IntBinop !IntBinop
             !Expr
             !Expr
  | IntComp !IntComp !Expr !Expr
  | VarRef !VarId
  | IntLit !Integer
  deriving (Show, Eq, Ord)

data AssgnLocation
  = VarLoc !VarId
  | ArrayEl !AssgnLocation
            !AssgnLocation
  deriving (Show, Eq, Ord)

data Stmt
  = Return !Expr
  | Assgn !AssgnLocation
          !Expr
  | VarDecl !TypedVar !Expr
  | If !Expr
       ![Stmt]
       !(Maybe [Stmt])
  | While !Expr ![Stmt]
  deriving (Show, Eq, Ord)
