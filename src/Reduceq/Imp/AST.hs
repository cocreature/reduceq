{-# LANGUAGE TemplateHaskell #-}
module Reduceq.Imp.AST
  ( VarId(..)
  , Decl(..)
  , Expr(..)
  , FunctionBody(..)
  , FunDecl(..)
  , IntBinop(..)
  , IntComp(..)
  , MatchClause(..)
  , Stmt(..)
  , Ty(..)
  , TypedVar(..)
  , funDeclTy
  , collectAssgnLocs
  , _Assgn
  , _VarDecl
  ) where

import Reduceq.Prelude

import Control.Lens
import Data.Data

newtype VarId = VarId { getVarId :: Text } deriving (Show, Eq, Ord, IsString, Data)

data Decl = FunDecl !FunDecl deriving (Show, Eq, Ord)

data Ty
  = TyUnit
  | TyInt
  | TyReal
  | TyBool
  | TyProd !Ty
           !Ty
  | TySum !Ty
          !Ty
  | TyArr !Ty
  | TyFun ![Ty]
          !Ty
  deriving (Show, Eq, Ord, Data)

data TypedVar = TypedVar
  { varName :: !VarId
  , varType :: !Ty
  } deriving (Show, Eq, Ord, Data)

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
  | Fst !Expr
  | Snd !Expr
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
  | ReadAtKey !Expr
              !Expr -- Read array key
  | Unit
  | Call !Expr
         !(NonEmpty Expr)
  | Lambda !(NonEmpty TypedVar)
           !Expr
  | EmptyArray
  deriving (Show, Eq, Ord, Data)

-- | @| var : ty => { stmts }@
data MatchClause =
  MatchClause !TypedVar
              ![Stmt]
  deriving (Show, Eq, Ord, Data)

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
  | ForEach !TypedVar
            !Expr
            ![Stmt] -- for (var : expr) { stmts }
  | Match !Expr
          !MatchClause
          !MatchClause
  deriving (Show, Eq, Ord, Data)

instance Plated Stmt where

makePrisms ''Stmt

collectAssgnLocs :: Fold Stmt VarId
collectAssgnLocs = cosmos . _Assgn . _1
