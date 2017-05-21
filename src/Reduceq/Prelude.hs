module Reduceq.Prelude
  ( module Protolude
  , NonEmpty(..)
  , foldr1
  , hPutStr
  , hPutStrLn
  , some1
  , uncurry3
  , assert
  ) where

import Data.Foldable (foldr1)
import Data.List.NonEmpty
import Data.Text.IO (hPutStr, hPutStrLn)
import Protolude hiding (Infix, try)
import Control.Exception (assert)

uncurry3 :: (a -> b -> c -> d) -> ((a, b, c) -> d)
uncurry3 f = \(a, b, c) -> f a b c
