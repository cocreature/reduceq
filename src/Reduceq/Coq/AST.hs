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
  , instantiate
  , shiftVars
  , simplify
  , closed
  , collectExternReferences
  ) where

import Reduceq.Prelude

import Control.Lens hiding ((&), index, op, List)
import Control.Monad.State.Strict
import Data.Data

import Reduceq.Imp (IntBinop(..), IntComp(..), ProgramSteps(..))

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
  | Length Expr
  | Range Expr Expr Expr
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
    go (Abs ty body) = Abs ty (substAt (succ id) (shiftVars substitute) body)
    go (Case c x y) =
      Case
        (go c)
        (substAt (succ id) (shiftVars substitute) x)
        (substAt (succ id) (shiftVars substitute) y)
    go e = over plate go e

instantiate :: Expr -> Expr -> Expr
instantiate substitute (unannotate -> Abs _ty body) =
  substAt (VarId 0) substitute body
instantiate _ expr =
  panic ("Tried to instantiate something that isn’t a binder: " <> show expr)

unannotate :: Expr -> Expr
unannotate (Annotated e _) = unannotate e
unannotate e = e

closed :: Expr -> Bool
closed expr = execState (closedUpTo (VarId 0) expr) True
  where closedUpTo :: VarId -> Expr -> State Bool ()
        closedUpTo id (Var id') = modify' (&& id > id')
        closedUpTo id (Abs _ body) = closedUpTo (succ id) body
        closedUpTo id (Case c x y) =
          closedUpTo id c >>
          closedUpTo (succ id) x >>
          closedUpTo (succ id) y
        closedUpTo id e = traverseOf_ plate (closedUpTo id) e

countReferences :: VarId -> Expr -> Int
countReferences varId expr = execState (go varId expr) 0
  where go :: VarId -> Expr -> State Int ()
        go id (Var id')
          | id == id' = modify' (+1)
          | otherwise = pure ()
        go id (Abs _ body) = go (succ id) body
        go id (Case c x y) =
          go id c >>
          go (succ id) x >>
          go (succ id) y
        go id e = traverseOf_ plate (go id) e

simplify :: Expr -> Expr
simplify =
  rewrite $ \e ->
    case e of
      (App (unannotate -> Abs _ty body) (unannotate -> lit@(IntLit _))) ->
        Just $ substAt (VarId 0) lit body
      (App (unannotate -> Abs ty body) (unannotate -> lit@(List _))) ->
        Just $ substAt (VarId 0) (lit `Annotated` ty) body
      (App (unannotate -> Abs ty (Var (VarId 0))) arg) ->
        Just (arg `Annotated` ty)
      (App (unannotate -> Abs ty body) arg)
        | countReferences (VarId 0) body <= 1 ->
          Just $ substAt (VarId 0) (arg `Annotated` ty) body
      _ -> Nothing
