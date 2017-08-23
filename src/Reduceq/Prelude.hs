module Reduceq.Prelude
  ( module Protolude
  , NonEmpty(..)
  , foldr1
  , some1
  , uncurry3
  , assert
  , (<>)
  ) where

import Data.Semigroup
import Control.Exception (assert)
import Data.Foldable (foldr1)
import Data.List.NonEmpty hiding ((!!))
import Protolude hiding (Prefix, Infix, from, try, list, to, execState, State, diff, (<>))

uncurry3 :: (a -> b -> c -> d) -> ((a, b, c) -> d)
uncurry3 f = \(a, b, c) -> f a b c
