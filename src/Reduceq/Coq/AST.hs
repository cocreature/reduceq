{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Reduceq.Coq.AST
  ( Expr(..)
  , Ann(..)
  , ExternReference(..)
  , Ty(..)
  , VarId(..)
  , IntBinop(..)
  , IntComp(..)
  , ProgramSteps(..)
  , TypedExpr
  , stripAnn
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

stripAnn :: Ann a e -> e
stripAnn (Ann _ e) = e

data Ann a e =
  Ann !a
      !e
  deriving (Show, Eq, Ord, Data, Typeable, Functor)

data Expr a
  = Var VarId
  | ExternRef !ExternReference
  | IntLit !Integer
  | App (Ann a (Expr a))
        (Ann a (Expr a))
  | Abs Ty
        (Maybe Imp.VarId) -- Name hint
        (Ann a (Expr a))
  | Fst (Ann a (Expr a))
  | Snd (Ann a (Expr a))
  | Pair (Ann a (Expr a))
         (Ann a (Expr a))
  | Inl (Ann a (Expr a))
  | Inr (Ann a (Expr a))
  | Case (Ann a (Expr a))
         (Ann a (Expr a))
         (Ann a (Expr a))
  | If (Ann a (Expr a))
       (Ann a (Expr a))
       (Ann a (Expr a))
  | IntBinop IntBinop
             (Ann a (Expr a))
             (Ann a (Expr a))
  | IntComp IntComp
            (Ann a (Expr a))
            (Ann a (Expr a))
  | Iter (Ann a (Expr a))
         (Ann a (Expr a)) -- The first argument is a function representing
                   -- the loop body and the second argument is the
                   -- initial value
  | Set (Ann a (Expr a))
        (Ann a (Expr a))
        (Ann a (Expr a)) -- Set array index val
  | SetAtKey (Ann a (Expr a))
             (Ann a (Expr a))
             (Ann a (Expr a)) -- Set map key val
  | Read (Ann a (Expr a))
         (Ann a (Expr a)) -- Read array index
  | ReadAtKey (Ann a (Expr a))
              (Ann a (Expr a)) -- Read map val
  | Unit
  | Annotated (Ann a (Expr a))
              Ty -- explicit type annotations
  | Map (Ann a (Expr a))
        (Ann a (Expr a))
  | Group (Ann a (Expr a))
  | Fold (Ann a (Expr a))
         (Ann a (Expr a))
         (Ann a (Expr a))
  | Concat (Ann a (Expr a))
  | Length (Ann a (Expr a))
  | Range (Ann a (Expr a))
          (Ann a (Expr a))
          (Ann a (Expr a))
  | Replicate (Ann a (Expr a))
              (Ann a (Expr a))
  | Zip (Ann a (Expr a)) (Ann a (Expr a))
  | List [(Ann a (Expr a))]
  | LiftN Word
          (Ann a (Expr a))
  deriving (Show, Eq, Ord, Data, Typeable)

instance Functor Expr where
  fmap f (App (Ann a e) (Ann a' e')) = App (Ann (f a) (f <$> e)) (Ann (f a') (f <$> e'))

makePrisms ''Expr

collectExternReferences :: Data a => Expr a -> [ExternReference]
collectExternReferences e = e ^.. cosmos . _ExternRef

instance (Data a, Data e) => Plated (Ann a e)
instance Data a => Plated (Expr a)

-- | Increment free DeBruijn indices greater or equal than m by n
liftVarsAbove :: Data a => Word -> Word -> Ann a (Expr a) -> Ann a (Expr a)
liftVarsAbove m n expr = go expr
  where
    go (Ann a (Var (VarId index name)))
      | index >= m = Ann a (Var (VarId (index + n) name))
      | otherwise = Ann a (Var (VarId index name))
    go ref@(Ann a (ExternRef _)) = Ann a (LiftN n ref)
    go (Ann a (Abs ty name body)) =
      Ann a (Abs ty name (liftVarsAbove (succ m) n body))
    go (Ann a (Case c x y)) =
      (Ann
         a
         (Case (go c) (liftVarsAbove (succ m) n x) (liftVarsAbove (succ m) n y)))
    go e = e & plate %~ go

lift1 :: Data a => Ann a (Expr a) -> Ann a (Expr a)
lift1 = liftVarsAbove 0 1

substAt :: Data a => VarId -> Ann a (Expr a) -> Ann a (Expr a) -> Ann a (Expr a)
substAt id substitute expr = go expr
  where
    go (Ann a (Var id'))
      | id == id' = substitute
      | id' > id = Ann a (Var (pred id'))
      | otherwise = Ann a (Var id')
    go (Ann a (Abs ty name body)) =
      Ann a (Abs ty name (substAt (succ id) (lift1 substitute) body))
    go (Ann a (Case c x y)) =
      Ann
        a
        (Case
           (go c)
           (substAt (succ id) (lift1 substitute) x)
           (substAt (succ id) (lift1 substitute) y))
    go e = over plate go e

instantiate :: (Show a, Data a) => Ann a (Expr a) -> Ann a (Expr a) -> Ann a (Expr a)
instantiate substitute (unannotate . stripAnn -> Abs _ty _name body) =
  substAt (VarId 0 Nothing) substitute body
instantiate _ expr =
  panic ("Tried to instantiate something that isn’t a binder: " <> show expr)

unannotate :: Expr a -> Expr a
unannotate (Annotated e _) = unannotate (stripAnn e)
unannotate e = e

closed :: Data a => Expr a -> Bool
closed expr = execState (closedUpTo (VarId 0 Nothing) expr) True
  where
    closedUpTo id (Var id') = modify' (&& id > id')
    closedUpTo id (Abs _ _ body) = closedUpTo (succ id) (stripAnn body)
    closedUpTo id (Case c x y) =
      closedUpTo id (stripAnn c) >> closedUpTo (succ id) (stripAnn x) >>
      closedUpTo (succ id) (stripAnn y)
    closedUpTo id e = traverseOf_ plate (closedUpTo id) e

countReferences :: Data a => VarId -> Expr a -> Int
countReferences varId expr = execState (go varId expr) 0
  where go id (Var id')
          | id == id' = modify' (+1)
          | otherwise = pure ()
        go id (Abs _ _ body) = go (succ id) (stripAnn body)
        go id (Case c x y) =
          go id (stripAnn c) >>
          go (succ id) (stripAnn x) >>
          go (succ id) (stripAnn y)
        go id e = traverseOf_ plate (go id) e

simplify :: (Data a) => Ann a (Expr a) -> Ann a (Expr a)
simplify =
  rewrite $ \e ->
    case e of
      (Ann _ (App (unannotate . stripAnn -> Abs _ty _name body) (fmap unannotate -> lit@(Ann _ (IntLit _))))) ->
        Just $ substAt (VarId 0 Nothing) lit body
      (Ann _ (App (unannotate . stripAnn -> Abs ty _name body) (fmap unannotate -> lit@(Ann a (List _))))) ->
        Just $ substAt (VarId 0 Nothing) (Ann a (lit `Annotated` ty)) body
      (Ann _ (App (unannotate . stripAnn -> Abs ty _name (Ann _ (Var (VarId 0 _)))) arg@(Ann a _))) ->
        Just (Ann a (arg `Annotated` ty))
      (Ann a (App (unannotate . stripAnn -> Abs ty _name body) (fmap unannotate -> ref@(Ann _ (ExternRef (ExternReference _ ty')))))) ->
        assert (ty == ty') $ Just $ substAt (VarId 0 Nothing) ref body
      (Ann _ (App (unannotate . stripAnn -> Abs _ty _name body) arg@(Ann a _)))
        | countReferences (VarId 0 Nothing) (stripAnn body) <= 1 ->
          Just (substAt (VarId 0 Nothing) arg body)
      _ -> Nothing

stripLift :: Expr a -> Expr a
stripLift (LiftN _ e) = stripLift (stripAnn e)
stripLift e = e

stripExternLifts :: Data a => (Text -> Bool) -> Expr a -> Expr a
stripExternLifts isExtern (stripLift -> ref@(ExternRef (ExternReference name _)))
  | isExtern name = ref
stripExternLifts isExtern e = over plate (stripExternLifts isExtern) e

type TypedExpr = Ann Ty (Expr Ty)
