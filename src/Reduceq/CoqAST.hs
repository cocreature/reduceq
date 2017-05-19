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
  | TySum Ty
          Ty
  | TyArr Ty
  | TyFun Ty
          Ty
  deriving (Show, Eq, Ord, Data, Typeable)

data Expr a
  = Var a
  | IntLit !Integer
  | App (Expr a)
        (Expr a)
  | Abs Ty
        (Expr a)
  | Fst (Expr a)
  | Snd (Expr a)
  | Pair (Expr a)
         (Expr a)
  | Inl (Expr a)
  | Inr (Expr a)
  | Case (Expr a)
         (Expr a)
         (Expr a)
  | If (Expr a)
       (Expr a)
       (Expr a)
  | IntBinop IntBinop
             (Expr a)
             (Expr a)
  | IntComp IntComp
            (Expr a)
            (Expr a)
  | Iter (Expr a)
         (Expr a) -- The first argument is a function representing
                   -- the loop body and the second argument is the
                   -- initial value
  | Set (Expr a)
        (Expr a)
        (Expr a) -- Set array index val
  | SetAtKey (Expr a)
             (Expr a)
             (Expr a) -- Set map key val
  | Read (Expr a)
         (Expr a) -- Read array index
  | ReadAtKey (Expr a)
              (Expr a) -- Read map val
  | Unit
  deriving (Show, Eq, Ord, Data, Typeable)

instance Data a => Plated (Expr a)

-- | Increment free DeBruijn indices greater or equal than m by n
liftVarsAbove :: Word -> Word -> Expr VarId -> Expr VarId
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
    go (Set a i v) = Set (go a) (go i) (go v)
    go (SetAtKey a k v) = Set (go a) (go k) (go v)
    go (Read a i) = Read (go a) (go i)
    go (ReadAtKey a k) = ReadAtKey (go a) (go k)

shiftVars :: Expr VarId -> Expr VarId
shiftVars = liftVarsAbove 0 1

substAt :: VarId -> Expr VarId -> Expr VarId -> Expr VarId
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

betaReduce :: Expr VarId -> Expr VarId
betaReduce =
  transform $ \e ->
    case e of
      (App (Abs _ body) lit@(IntLit _)) -> substAt (VarId 0) lit body
      _ -> e
