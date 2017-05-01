module Reduceq.CoqAST
  ( Expr(..)
  , Ty(..)
  , VarId(..)
  , IntBinop(..)
  , IntComp(..)
  , liftVarsAbove
  , shiftVars
  ) where

import Reduceq.Prelude

import Reduceq.AST (IntBinop(..), IntComp(..))

-- | DeBruijn indices
newtype VarId =
  VarId Word
  deriving (Show, Eq, Ord)

data Ty
  = TyInt
  | TyBool
  | TyUnit
  | TyProd Ty
           Ty
  deriving (Show, Eq, Ord)

data Expr
  = Var VarId
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
  deriving (Show, Eq, Ord)

-- | Increment free DeBruijn indices greater or equal than m by n
liftVarsAbove :: Word -> Word -> Expr -> Expr
liftVarsAbove m n e = go e
  where
    go (Var (VarId index))
      | index >= m = Var (VarId (index + n))
      | otherwise = Var (VarId index)
    go (App x y) = App (go x) (go y)
    go (Abs ty body) = go (Abs ty (liftVarsAbove (succ m) n body))
    go (Fst x) = Fst (go x)
    go (Snd x) = Snd (go x)
    go (Pair x y) = Pair (go x) (go y)
    go (Inl x) = Inl (go x)
    go (Inr x) = Inr (go x)
    go (Case c x y) =
      Case (go c) (liftVarsAbove (succ m) n x) (liftVarsAbove (succ m) n y)

shiftVars :: Expr -> Expr
shiftVars = liftVarsAbove 0 1
