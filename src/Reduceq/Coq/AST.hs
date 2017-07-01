{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Reduceq.Coq.AST
  ( Expr(..)
  , ExternReference(..)
  , Ty(..)
  , VarId(..)
  , IntBinop(..)
  , IntComp(..)
  , ProgramSteps(..)
  , liftVarsAbove
  , shiftVars
  , betaReduce
  , collectExternReferences
  ) where

import Reduceq.Prelude

import Reduceq.Imp (IntBinop(..), IntComp(..), ProgramSteps(..))

import Control.Lens hiding ((&), index, op, List)
import Data.Data

-- | DeBruijn indices
newtype VarId =
  VarId Word
  deriving (Show, Eq, Ord, Enum, Data, Typeable)

data Ty
  = TyInt
  | TyReal
  | TyBool
  | TyUnit
  | TyProd Ty
           Ty
  | TySum Ty
          Ty
  | TyArr Ty
  | TyFun Ty
          Ty
  deriving (Show, Eq, Ord, Data, Typeable)

data ExternReference = ExternReference
  { refName :: !Text
  , refType :: !Ty
  } deriving (Show, Eq, Ord, Data, Typeable)

data Expr
  = Var VarId
  | ExternRef !ExternReference
  | IntLit !Integer
  | App Expr
        Expr
  | Abs Ty
        Expr
  | Fst Expr
  | Snd Expr
  | Pair Expr
         Expr
  | Inl Expr
  | Inr Expr
  | Case Expr
         Expr
         Expr
  | If Expr
       Expr
       Expr
  | IntBinop IntBinop
             Expr
             Expr
  | IntComp IntComp
            Expr
            Expr
  | Iter Expr
         Expr -- The first argument is a function representing
                   -- the loop body and the second argument is the
                   -- initial value
  | Set Expr
        Expr
        Expr -- Set array index val
  | SetAtKey Expr
             Expr
             Expr -- Set map key val
  | Read Expr
         Expr -- Read array index
  | ReadAtKey Expr
              Expr -- Read map val
  | Unit
  | Annotated Expr
              Ty -- explicit type annotations
  | Map Expr
        Expr
  | Group Expr
  | Fold Expr
         Expr
         Expr
  | Concat Expr
  | List [Expr]
  deriving (Show, Eq, Ord, Data, Typeable)

makePrisms ''Expr

collectExternReferences :: Expr -> [ExternReference]
collectExternReferences e = e ^.. cosmos . _ExternRef

instance Plated Expr

-- | Increment free DeBruijn indices greater or equal than m by n
liftVarsAbove :: Word -> Word -> Expr -> Expr
liftVarsAbove m n expr = go expr
  where
    go (Var (VarId index))
      | index >= m = Var (VarId (index + n))
      | otherwise = Var (VarId index)
    go (Abs ty body) = go (Abs ty (liftVarsAbove (succ m) n body))
    go (Case c x y) =
      Case (go c) (liftVarsAbove (succ m) n x) (liftVarsAbove (succ m) n y)
    go e = e & plate %~ go

shiftVars :: Expr -> Expr
shiftVars = liftVarsAbove 0 1

substAt :: VarId -> Expr -> Expr -> Expr
substAt id substitute expr = go expr
  where
    go (Var id')
      | id == id' = substitute
      | id' > id = Var (pred id')
      | otherwise = Var id'
    go (Abs ty body) = Abs ty (substAt (succ id) substitute body)
    go (Case c x y) =
      Case
        (go c)
        (substAt (succ id) substitute x)
        (substAt (succ id) substitute y)
    go e = over plate go e

unannotate :: Expr -> Expr
unannotate = transform $ \e ->
  case e of
    Annotated e' _ -> e'
    _ -> e

betaReduce :: Expr -> Expr
betaReduce =
  transform $ \e ->
    case e of
      (App (Abs ty body) (unannotate -> lit@(IntLit _))) ->
        substAt (VarId 0) lit body `Annotated` ty
      (App (Abs ty body) (unannotate -> lit@(List _))) ->
        substAt (VarId 0) lit body `Annotated` ty
      (App (Abs ty (Var (VarId 0))) arg) -> arg `Annotated` ty
      _ -> e
