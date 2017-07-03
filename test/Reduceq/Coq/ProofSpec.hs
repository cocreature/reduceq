module Reduceq.Coq.ProofSpec
  ( coqProofSpec
  ) where

import Reduceq.Prelude

import Test.Hspec

import Reduceq.Coq
import Reduceq.Imp.Parser (fileParser, stepsFileParser)

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
  describe "generate proof obligation for steps" $ do
    it "generates correct Coq file for example 1" $ do
      input <-
        liftIO (readFile "test/data/proofspec/prove_steps/wordcount/input")
      withParseResult stepsFileParser input $ \steps ->
        withTransformedSteps steps $ \transformed ->
          let reduced = fmap simplify transformed
          in withStepsType reduced $ \ty ->
               case pprintProofStepsObligation reduced ty of
                 Left err -> (expectationFailure . toS . showPprintError) err
                 Right doc ->
                   displayDoc doc `shouldBeFile`
                   "test/data/proofspec/prove_steps/wordcount/output"

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
