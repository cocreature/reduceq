module Reduceq.AST
  ( VarId(..)
  , Decl(..)
  , Expr(..)
  , FunctionBody(..)
  , FunDecl(..)
  , IntBinop(..)
  , IntComp(..)
  , Stmt(..)
  , Ty(..)
  , TypedVar(..)
  , funDeclTy
  ) where

import Reduceq.Prelude

import Data.Data

newtype VarId = VarId Text deriving (Show, Eq, Ord, IsString)

data Decl = FunDecl !FunDecl deriving (Show, Eq, Ord)

data Ty
  = TyInt
  | TyReal
  | TyBool
  | TyProd !Ty !Ty
  | TySum !Ty !Ty
  | TyArr !Ty
  | TyFun ![Ty]
          !Ty
  deriving (Show, Eq, Ord)

data TypedVar = TypedVar
  { varName :: !VarId
  , varType :: !Ty
  } deriving (Show, Eq, Ord)

data FunctionBody
  = ExternFunction
  | FunctionBody ![Stmt]
  deriving (Show, Eq, Ord)

data FunDecl = FunctionDeclaration
  { funName :: !VarId
  , funArguments :: [TypedVar]
  , funReturnType :: !Ty
  , funBody :: !FunctionBody
  } deriving (Show, Eq, Ord)

funDeclTy :: FunDecl -> Ty
funDeclTy (FunctionDeclaration _ args retTy _) = TyFun (map varType args) retTy

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
  | IntComp !IntComp
            !Expr
            !Expr
  | VarRef !VarId
  | IntLit !Integer
  | Pair !Expr
         !Expr
  | Inl !Expr
  | Inr !Expr
  | Set !Expr
        !Expr
        !Expr -- Set array index val
  | SetAtKey !Expr
             !Expr
             !Expr -- SetAtKey map key val
  | Read !Expr
         !Expr -- Read array index
  | ReadAtKey !Expr !Expr -- Read array key
  | Unit
  | Call !Expr
         !(NonEmpty Expr)
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
