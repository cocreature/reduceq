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
  , substAt
  , lift1
  , simplify
  , closed
  , collectExternReferences
  , unannotate
  , stripExternLifts
  ) where

import           Reduceq.Prelude

import           Control.Lens hiding ((&), index, op, List)
import           Control.Monad.State.Strict
import           Data.Data

import qualified Reduceq.Imp as Imp
import           Reduceq.Imp (IntBinop(..), IntComp(..), ProgramSteps(..))

-- | DeBruijn indices
data VarId = VarId
  { varId :: Word
  , nameHint :: !(Maybe Text)
  } deriving (Show, Data, Typeable)

instance Eq VarId where
  (==) = (==) `on` varId

instance Ord VarId where
  compare = compare `on` varId

instance Enum VarId where
  toEnum i = VarId (toEnum i) Nothing
  fromEnum (VarId id _) = fromEnum id

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
        (Maybe Imp.VarId) -- Name hint
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
  | Replicate Expr Expr
  | List [Expr]
  | LiftN Word Expr
  deriving (Show, Eq, Ord, Data, Typeable)

makePrisms ''Expr

collectExternReferences :: Expr -> [ExternReference]
collectExternReferences e = e ^.. cosmos . _ExternRef

instance Plated Expr

-- | Increment free DeBruijn indices greater or equal than m by n
liftVarsAbove :: Word -> Word -> Expr -> Expr
liftVarsAbove m n expr = go expr
  where
    go (Var (VarId index name))
      | index >= m = Var (VarId (index + n) name)
      | otherwise = Var (VarId index name)
    go ref@(ExternRef _) = LiftN n ref
    go (Abs ty name body) = Abs ty name (liftVarsAbove (succ m) n body)
    go (Case c x y) =
      Case (go c) (liftVarsAbove (succ m) n x) (liftVarsAbove (succ m) n y)
    go e = e & plate %~ go

lift1 :: Expr -> Expr
lift1 = liftVarsAbove 0 1

substAt :: VarId -> Expr -> Expr -> Expr
substAt id substitute expr = go expr
  where
    go (Var id')
      | id == id' = substitute
      | id' > id = Var (pred id')
      | otherwise = Var id'
    go (Abs ty name body) = Abs ty name (substAt (succ id) (lift1 substitute) body)
    go (Case c x y) =
      Case
        (go c)
        (substAt (succ id) (lift1 substitute) x)
        (substAt (succ id) (lift1 substitute) y)
    go e = over plate go e

instantiate :: Expr -> Expr -> Expr
instantiate substitute (unannotate -> Abs _ty _name body) =
  substAt (VarId 0 Nothing) substitute body
instantiate _ expr =
  panic ("Tried to instantiate something that isn’t a binder: " <> show expr)

unannotate :: Expr -> Expr
unannotate (Annotated e _) = unannotate e
unannotate e = e

closed :: Expr -> Bool
closed expr = execState (closedUpTo (VarId 0 Nothing) expr) True
  where closedUpTo :: VarId -> Expr -> State Bool ()
        closedUpTo id (Var id') = modify' (&& id > id')
        closedUpTo id (Abs _ _ body) = closedUpTo (succ id) body
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
        go id (Abs _ _ body) = go (succ id) body
        go id (Case c x y) =
          go id c >>
          go (succ id) x >>
          go (succ id) y
        go id e = traverseOf_ plate (go id) e

simplify :: Expr -> Expr
simplify =
  rewrite $ \e ->
    case e of
      (App (unannotate -> Abs _ty _name body) (unannotate -> lit@(IntLit _))) ->
        Just $ substAt (VarId 0 Nothing) lit body
      (App (unannotate -> Abs ty _name body) (unannotate -> lit@(List _))) ->
        Just $ substAt (VarId 0 Nothing) (lit `Annotated` ty) body
      (App (unannotate -> Abs ty _name (Var (VarId 0 _))) arg) ->
        Just (arg `Annotated` ty)
      (App (unannotate -> Abs ty _name body) (unannotate -> ref@(ExternRef (ExternReference _ ty')))) ->
        assert (ty == ty') $ Just $ substAt (VarId 0 Nothing) ref body
      (App (unannotate -> Abs ty _name body) arg)
        | countReferences (VarId 0 Nothing) body <= 1 ->
          Just $ substAt (VarId 0 Nothing) (arg `Annotated` ty) body
      _ -> Nothing

stripLift :: Expr -> Expr
stripLift (LiftN _ e) = stripLift e
stripLift e = e

stripExternLifts :: (Text -> Bool) -> Expr -> Expr
stripExternLifts isExtern (stripLift -> ref@(ExternRef (ExternReference name _)))
  | isExtern name = ref
stripExternLifts isExtern e = over plate (stripExternLifts isExtern) e
