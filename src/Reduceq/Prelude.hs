module Reduceq.Prelude
  ( module Protolude
  , NonEmpty(..)
  , foldr1
  , hPutStr
  , hPutStrLn
  , some1
  ) where

import Data.Foldable (foldr1)
import Data.List.NonEmpty
import Data.Text.IO (hPutStr, hPutStrLn)
import Protolude hiding (Infix, try)
