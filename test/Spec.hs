import Reduceq.Prelude

import Test.Hspec

import Reduceq.Coq.ProofSpec
import Reduceq.Coq.TypingSpec
import Reduceq.Imp.ParserSpec
import Reduceq.TransformSpec

main :: IO ()
main =
  hspec $ do
    parserSpec
    transformSpec
    reducedTransformSpec
    typeInferenceSpec
    coqProofSpec
