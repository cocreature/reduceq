module Reduceq.Spec.Util
  ( withParseResult
  , withTransformed
  , withType
  , withTypedReduced
  , expectParseResult
  , parseError
  ) where

import           Reduceq.Prelude

import           Test.Hspec

import qualified Reduceq.Coq as Coq
import           Reduceq.Coq.Typing
import qualified Reduceq.Imp as Imp
import           Reduceq.Imp.Parser
import           Reduceq.Transform

parseError :: ErrInfo -> Expectation
parseError = expectationFailure . toS . renderParseError

withTransformed :: NonEmpty Imp.FunDecl -> (Coq.Expr Coq.VarId -> Expectation) -> Expectation
withTransformed decls cont =
  case runTransformM (transformDecls decls) of
    Left err -> expectationFailure (toS (showTransformError err))
    Right transformed -> cont transformed

withParseResult :: (Show a, Eq a) => Parser a -> Text -> (a -> Expectation) -> Expectation
withParseResult parser input cont =
  case parseText parser mempty input of
    Success result -> cont result
    Failure errInfo -> parseError errInfo

withType :: Coq.Expr Coq.VarId -> (Coq.Ty -> Expectation) -> Expectation
withType expr cont =
  case runInferM (inferType expr) of
    Left err -> (expectationFailure . toS . Coq.displayCompact . showInferError) err
    Right ty -> cont ty

withTypedReduced :: Text -> (Coq.Expr Coq.VarId  -> Coq.Ty -> Expectation) -> Expectation
withTypedReduced input cont =
  withParseResult fileParser input $ \decls ->
    withTransformed decls $ \transformed ->
      let reduced = Coq.betaReduce transformed
      in withType reduced $ \ty -> cont reduced ty

expectParseResult :: (Show a, Eq a) => Parser a -> Text -> a -> Expectation
expectParseResult parser input result =
  withParseResult parser input (`shouldBe` result)
