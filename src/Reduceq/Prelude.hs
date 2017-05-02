module Reduceq.Prelude
  ( module Protolude
  , foldr1
  , hPutStr
  , hPutStrLn
  ) where

import Data.Foldable (foldr1)
import Data.Text.IO (hPutStr, hPutStrLn)
import Protolude hiding (Infix, try)
