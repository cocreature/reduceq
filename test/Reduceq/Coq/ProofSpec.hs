module Reduceq.Coq.ProofSpec
  ( coqProofSpec
  ) where

import Reduceq.Prelude

import Test.Hspec

import Reduceq.Coq
import Reduceq.Imp.Parser (fileParser)

import Reduceq.Spec.Util

coqProofSpec :: Spec
coqProofSpec = do
  describe "generate example" $
    withTestsFromFile
      "test/data/proofspec/prove_single"
      (\i -> "generates the correct Coq file for example " <> show i)
      (\[inp, outp] -> testProofSingleSpec inp outp)
  describe "generate proof obligation" $
    withTestsFromFile
      "test/data/proofspec/prove"
      (\i -> "generates the correct Coq proof obligation for example " <> show i)
      (\[inp1, inp2, outp] -> testProofSpec inp1 inp2 outp)

testProofSingleSpec :: Text -> Text -> Expectation
testProofSingleSpec input output =
  withParseResult fileParser input $ \decls ->
    withTransformed decls $ \transformed ->
      let reduced = simplify transformed
      in withType reduced $ \ty ->
           displayDoc (pprintExample reduced ty) `shouldBe` output

testProofSpec :: Text -> Text -> Text -> Expectation
testProofSpec imperativeInp mapreduceInp output =
  withTypedReduced imperativeInp $ \imperative imperativeTy ->
    withTypedReduced mapreduceInp $ \mapreduce mapreduceTy ->
      case (pprintProofObligation
              (imperative, imperativeTy)
              (mapreduce, mapreduceTy)) of
        Left err -> (expectationFailure . toS . showPprintError) err
        Right doc -> displayDoc doc `shouldBe` output
