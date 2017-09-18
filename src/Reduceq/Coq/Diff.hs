{-# OPTIONS_GHC -fmax-pmcheck-iterations=10000000 #-}
{-# LANGUAGE ViewPatterns #-}
module Reduceq.Coq.Diff
  ( Diff(..)
  , Morphism(..)
  , diff
  , pruneDiff
  , substInDiff
  ) where

import Reduceq.Prelude

import Reduceq.Coq.AST

data Morphism
  = MFst
  | MSnd
  | MIter
  | MApp
  | MIf
  | MInr
  | MInl
  | MPair
  deriving (Show, Eq, Ord)

data Diff e
  = Equal
  | Different !e
              !e
              !Ty
  | DifferentFun !e
                 !e
                 !Ty
                 !Ty
                 (Diff e)
  | DifferentMor !Morphism [Diff e]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

diff :: TypedExpr -> TypedExpr -> Diff TypedExpr
diff (Ann _ (Annotated e _)) e' = diff e e'
diff e (Ann _ (Annotated e' _)) = diff e e'
diff f@(Ann (TyFun dom ran) (Abs ty _ body)) g@(Ann (TyFun dom' ran') (Abs ty' _ body'))
  | dom == dom' && ran == ran' && ty == ty' && ty == dom =
    DifferentFun f g dom ran (diff body body')
diff (stripAnn -> (Fst x@(Ann (TyProd a b) _))) (stripAnn -> Fst y@(Ann (TyProd a' b') _))
  | a == a' && b == b' = DifferentMor MFst [diff x y]
diff (stripAnn -> (Snd x@(Ann (TyProd a b) _))) (stripAnn -> Snd y@(Ann (TyProd a' b') _))
  | a == a' && b == b' = DifferentMor MSnd [diff x y]
diff (Ann t' (Iter f x)) (Ann t (Iter g y)) =
  assert (t == t') (DifferentMor MIter [diff f g, diff x y])
diff e@(Ann t (App f@(Ann funTy _) x)) e'@(Ann t' (App f'@(Ann funTy' _) x'))
  | funTy == funTy' =
    assert (t == t') (DifferentMor MApp [diff f f', diff x x'])
  | otherwise = assert (t == t') (Different e e' t)
diff (Ann t (If a b c)) (Ann t' (If a' b' c')) =
  assert
    (t == t')
    (DifferentMor MIf (map (uncurry diff) [(a, a'), (b, b'), (c, c')]))
diff (Ann t (Inr x)) (Ann t' (Inr x')) =
  assert (t == t') $ DifferentMor MInr [diff x x']
diff (Ann t (Inl x)) (Ann t' (Inl x')) =
  assert (t == t') $ DifferentMor MInl [diff x x']
diff (Ann t (Pair x y)) (Ann t' (Pair x' y')) =
  assert (t == t') $ DifferentMor MPair [diff x x', diff y y']
diff (Ann t x) (Ann t' x')
  | x == x' = Equal
  | otherwise = assert (t == t') $ Different (Ann t x) (Ann t' x') t

pruneDiff :: Eq e => Diff e -> Diff e
pruneDiff Equal = Equal
pruneDiff (DifferentFun x y dom ran d) =
  case pruneDiff d of
    Equal -> Equal
    d' -> DifferentFun x y dom ran d'
pruneDiff (Different t x y) = Different t x y
pruneDiff (DifferentMor m args) =
  case filter (/= Equal) (pruneDiff <$> args) of
    [] -> Equal
    args' -> DifferentMor m args'

substInDiff :: VarId -> TypedExpr -> Diff TypedExpr -> Diff TypedExpr
substInDiff !id substitute d = go d
  where
    go Equal = Equal
    go (DifferentFun f g dom ran d') =
      DifferentFun
        (substAt id substitute f)
        (substAt id substitute g)
        dom
        ran
        (substInDiff (succ id) (lift1 substitute) d')
    go (Different x y t) =
      Different (substAt id substitute x) (substAt id substitute y) t
    go (DifferentMor m args) =
      DifferentMor m (go <$> args)
