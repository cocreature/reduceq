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

import Control.Exception (assert)
import Data.Foldable (foldr1)
import Data.List.NonEmpty hiding ((!!))
import Data.Text.IO (hPutStr, hPutStrLn)
import Protolude hiding (Prefix, Infix, from, try, list, to, execState, State)

uncurry3 :: (a -> b -> c -> d) -> ((a, b, c) -> d)
uncurry3 f = \(a, b, c) -> f a b c
