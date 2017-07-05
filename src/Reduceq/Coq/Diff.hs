module Reduceq.Coq.Diff
  ( Diff(..)
  , diff
  , diffSteps
  , pruneDiff
  , substInDiff
  ) where

import Reduceq.Prelude

import Reduceq.Coq.AST

data Diff e
  = Equal
  | Different !e
              !e
  | DifferentFun !e
                 !e
                 !Ty
                 (Diff e)
  | DifferentArgs [Diff e]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

diff :: Expr -> Expr -> Diff Expr
diff (Annotated e _) e' = diff e e'
diff e (Annotated e' _) = diff e e'
diff x@(Abs ty _ body) y@(Abs ty' _ body') =
  assert (ty == ty') (DifferentFun x y ty (diff body body'))
diff (Fst x) (Fst y) = diff x y
diff (Snd x) (Snd y) = diff x y
diff (Iter f x) (Iter g y) = DifferentArgs (map (uncurry diff) [(f, g), (x, y)])
diff (App f x) (App f' x') = DifferentArgs [diff f f', diff x x']
diff (If a b c) (If a' b' c') =
  DifferentArgs (map (uncurry diff) [(a, a'), (b, b'), (c, c')])
diff (Inr x) (Inr x') = diff x x'
diff (Inl x) (Inl x') = diff x x'
diff (Pair x y) (Pair x' y') = DifferentArgs [diff x x', diff y y']
diff x y
  | x == y = Equal
  | otherwise = Different x y

diffSteps :: ProgramSteps Expr -> [Diff Expr]
diffSteps (ProgramSteps initial steps final) =
  zipWith diff (initial : steps) (steps ++ [final])

pruneDiff :: Diff Expr -> Diff Expr
pruneDiff Equal = Equal
pruneDiff (DifferentFun x y ty d) =
  case pruneDiff d of
    Equal -> Equal
    d' -> DifferentFun x y ty d'
pruneDiff (Different x y) = Different x y
pruneDiff (DifferentArgs args) =
  case filter (/= Equal) (pruneDiff <$> args) of
    [] -> Equal
    args' -> DifferentArgs args'

substInDiff :: VarId -> Expr -> Diff Expr -> Diff Expr
substInDiff !id substitute d = go d
  where
    go Equal = Equal
    go (DifferentFun f g ty d') =
      DifferentFun
        (substAt id substitute f)
        (substAt id substitute g)
        ty
        (substInDiff (succ id) (lift1 substitute) d')
    go (Different x y) =
      Different (substAt id substitute x) (substAt id substitute y)
    go (DifferentArgs args) = DifferentArgs (map go args)
