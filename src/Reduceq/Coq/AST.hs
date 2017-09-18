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

import           Control.Lens hiding ((&), index, op, List, Fold)
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
  fmap _ (Var id) = Var id
  fmap _ (ExternRef ref) = ExternRef ref
  fmap _ (IntLit i) = IntLit i
  fmap f (App (Ann a e) (Ann a' e')) =
    App (Ann (f a) (f <$> e)) (Ann (f a') (f <$> e'))
  fmap f (Abs t name (Ann a body)) = Abs t name (Ann (f a) (f <$> body))
  fmap f (Fst (Ann a e)) = Fst (Ann (f a) (f <$> e))
  fmap f (Snd (Ann a e)) = Snd (Ann (f a) (f <$> e))
  fmap f (Pair (Ann a e) (Ann a' e')) =
    Pair (Ann (f a) (f <$> e)) (Ann (f a') (f <$> e'))
  fmap f (Inl (Ann a e)) = Inl (Ann (f a) (f <$> e))
  fmap f (Inr (Ann a e)) = Inr (Ann (f a) (f <$> e))
  fmap f (Fold (Ann ga g) (Ann ia i) (Ann xsa xs)) =
    Fold (Ann (f ga) (f <$> g)) (Ann (f ia) (f <$> i)) (Ann (f xsa) (f <$> xs))
  fmap f (Case (Ann cAnn c) (Ann lAnn l) (Ann rAnn r)) =
    Case
      (Ann (f cAnn) (f <$> c))
      (Ann (f lAnn) (f <$> l))
      (Ann (f rAnn) (f <$> r))
  fmap f (If (Ann cAnn c) (Ann tAnn t) (Ann fAnn fa)) =
    If
      (Ann (f cAnn) (f <$> c))
      (Ann (f tAnn) (f <$> t))
      (Ann (f fAnn) (f <$> fa))
  fmap f (IntBinop op (Ann xAnn x) (Ann yAnn y)) =
    IntBinop op (Ann (f xAnn) (f <$> x)) (Ann (f yAnn) (f <$> y))
  fmap f (IntComp comp (Ann xAnn x) (Ann yAnn y)) =
    IntComp comp (Ann (f xAnn) (f <$> x)) (Ann (f yAnn) (f <$> y))
  fmap f (Iter (Ann gAnn g) (Ann iAnn i)) =
    Iter (Ann (f gAnn) (f <$> g)) (Ann (f iAnn) (f <$> i))
  fmap f (Set (Ann arrAnn arr) (Ann iAnn i) (Ann valAnn val)) =
    Set
      (Ann (f arrAnn) (f <$> arr))
      (Ann (f iAnn) (f <$> i))
      (Ann (f valAnn) (f <$> val))
  fmap f (SetAtKey (Ann xsAnn xs) (Ann iAnn i) (Ann xAnn x)) =
    SetAtKey
      (Ann (f xsAnn) (f <$> xs))
      (Ann (f iAnn) (f <$> i))
      (Ann (f xAnn) (f <$> x))
  fmap f (ReadAtKey (Ann xsAnn xs) (Ann iAnn i)) =
    ReadAtKey (Ann (f xsAnn) (f <$> xs)) (Ann (f iAnn) (f <$> i))
  fmap f (Read (Ann xsAnn xs) (Ann iAnn i)) =
    Read (Ann (f xsAnn) (f <$> xs)) (Ann (f iAnn) (f <$> i))
  fmap f (Annotated (Ann ann e) t) = Annotated (Ann (f ann) (f <$> e)) t
  fmap f (Map (Ann mapAnn mapper) (Ann xsAnn xs)) =
    Map (Ann (f mapAnn) (f <$> mapper)) (Ann (f xsAnn) (f <$> xs))
  fmap f (Group (Ann arrAnn arr)) = Group (Ann (f arrAnn) (f <$> arr))
  fmap f (Concat (Ann xssAnn xss)) = Concat (Ann (f xssAnn) (f <$> xss))
  fmap f (Length (Ann xsAnn xs)) = Length (Ann (f xsAnn) (f <$> xs))
  fmap f (Range (Ann xAnn x) (Ann yAnn y) (Ann zAnn z)) =
    Range
      (Ann (f xAnn) (f <$> x))
      (Ann (f yAnn) (f <$> y))
      (Ann (f zAnn) (f <$> z))
  fmap f (Replicate (Ann nAnn n) (Ann vAnn v)) =
    Replicate (Ann (f nAnn) (f <$> n)) (Ann (f vAnn) (f <$> v))
  fmap f (Zip (Ann xsAnn xs) (Ann ysAnn ys)) =
    Zip (Ann (f xsAnn) (f <$> xs)) (Ann (f ysAnn) (f <$> ys))
  fmap f (List xs) = List (map (\(Ann eAnn e) -> Ann (f eAnn) (f <$> e)) xs)
  fmap f (LiftN i (Ann eAnn e)) = LiftN i (Ann (f eAnn) (f <$> e))
  fmap _ Unit = Unit

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
      (Ann _ (App (unannotate . stripAnn -> Abs ty _name body) (fmap unannotate -> ref@(Ann _ (ExternRef (ExternReference _ ty')))))) ->
        assert (ty == ty') $ Just $ substAt (VarId 0 Nothing) ref body
      (Ann _ (App (unannotate . stripAnn -> Abs _ty _name body) arg@(Ann _ _)))
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
