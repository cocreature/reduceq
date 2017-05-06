module Reduceq.CoqAST
  ( Expr(..)
  , Ty(..)
  , VarId(..)
  , IntBinop(..)
  , IntComp(..)
  , liftVarsAbove
  , shiftVars
  , betaReduce
  ) where

import Reduceq.Prelude

import Reduceq.AST (IntBinop(..), IntComp(..))

import Control.Lens hiding (index, op)
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
  | TyArr Ty
  | TyFun Ty Ty
  deriving (Show, Eq, Ord, Data, Typeable)

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
  | Iter Expr
         Expr -- The first argument is a function representing
                   -- the loop body and the second argument is the
                   -- initial value
  | Set Expr
        Expr
        Expr -- Set array index val
  | Read Expr
         Expr
  | Unit
  deriving (Show, Eq, Ord, Data, Typeable)

instance Plated Expr

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
    go lit@(IntLit _) = lit
    go (If cond x y) = If (go cond) (go x) (go y)
    go (IntBinop op x y) = IntBinop op (go x) (go y)
    go (IntComp comp x y) = IntComp comp (go x) (go y)
    go Unit = Unit
    go (Iter body init) = Iter (go body) (go init)

shiftVars :: Expr -> Expr
shiftVars = liftVarsAbove 0 1

substAt :: VarId -> Expr -> Expr -> Expr
substAt id substitute e = go e
  where
    go (Var id')
      | id == id' = substitute
      | id' > id = Var (pred id')
      | otherwise = Var id'
    go (App x y) = App (go x) (go y)
    go (Abs ty body) = Abs ty (substAt (succ id) substitute body)
    go (Fst x) = Fst (go x)
    go (Snd x) = Snd (go x)
    go (Pair x y) = Pair (go x) (go y)
    go (Inl x) = Inl (go x)
    go (Inr x) = Inr (go x)
    go (Case c x y) =
      Case
        (go c)
        (substAt (succ id) substitute x)
        (substAt (succ id) substitute y)
    go (IntBinop op x y) = IntBinop op (go x) (go y)
    go (IntComp comp x y) = IntComp comp (go x) (go y)
    go lit@(IntLit _) = lit
    go (If cond ifTrue ifFalse) = If (go cond) (go ifTrue) (go ifFalse)
    go Unit = Unit
    go (Iter body init) = Iter (go body) (go init)

betaReduce :: Expr -> Expr
betaReduce =
  transform $ \e ->
    case e of
      (App (Abs _ body) lit@(IntLit _)) -> substAt (VarId 0) lit body
      _ -> e
