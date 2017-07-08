{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Reduceq.Spec.Util
  ( withParseResult
  , withTransformed
  , withTransformedSteps
  , withType
  , withStepsType
  , withTypedReduced
  , expectParseResult
  , parseError
  , shouldBeFile
  , withTestsFromFile
  ) where

import           Reduceq.Prelude

import qualified Control.Foldl as Foldl
import           Control.Lens
import qualified Data.List.Split as List
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import           Pipes
import           Pipes.Group
import qualified Pipes.Parse as Pipes
import qualified Pipes.Prelude as Pipes
import qualified Pipes.Prelude.Text as Pipes
import           Pipes.Text.IO
import           Test.Hspec

import qualified Reduceq.Coq as Coq
import           Reduceq.Coq.Typing
import qualified Reduceq.Imp as Imp
import           Reduceq.Imp.Parser
import           Reduceq.Transform

parseError :: ErrInfo -> Expectation
parseError = expectationFailure . toS . renderParseError

withTransformed' :: (a -> TransformM b) -> a -> (b -> Expectation) -> Expectation
withTransformed' f original cont =
  case runTransformM (f original) of
    Left err -> expectationFailure (toS (showTransformError err))
    Right transformed -> cont transformed

withTransformed :: NonEmpty Imp.FunDecl -> (Coq.Expr () -> Expectation) -> Expectation
withTransformed = withTransformed' (fmap Coq.stripAnn . transformDecls)

withTransformedSteps :: Imp.ProgramSteps Imp.Program -> (Coq.ProgramSteps (Coq.Expr ()) -> Expectation) -> Expectation
withTransformedSteps = withTransformed' transformProgramSteps

withParseResult :: (Show a, Eq a) => Parser a -> Text -> (a -> Expectation) -> Expectation
withParseResult parser input cont =
  case parseText parser mempty input of
    Success result -> cont result
    Failure errInfo -> parseError errInfo

withType :: Coq.Ann () (Coq.Expr ()) -> (Coq.TypedExpr -> Expectation) -> Expectation
withType (Coq.Ann _ expr) cont =
  case runInferM (inferType expr) of
    Left err -> (expectationFailure . toS . Coq.displayCompact . showInferError) err
    Right ty -> cont ty

withStepsType :: Coq.ProgramSteps (Coq.Ann () (Coq.Expr ())) -> (Coq.ProgramSteps Coq.TypedExpr -> Expectation) -> Expectation
withStepsType expr cont =
  case runInferM (inferStepsType (Coq.stripAnn <$> expr)) of
    Left err -> (expectationFailure . toS . Coq.displayCompact . showInferError) err
    Right expr -> cont expr

withTypedReduced :: Text -> (Coq.TypedExpr -> Expectation) -> Expectation
withTypedReduced input cont =
  withParseResult fileParser input $ \decls ->
    withTransformed decls $ \transformed ->
      let reduced = Coq.simplify (Coq.Ann () transformed)
      in withType reduced $ \e -> cont e

expectParseResult :: (Show a, Eq a) => Parser a -> Text -> a -> Expectation
expectParseResult parser input result =
  withParseResult parser input (`shouldBe` result)

-- TODO make a PR to pipes-group for this function
wordsBy ::
     forall m a' a x. Monad m
  => (a' -> Bool)
  -> Lens (Producer a' m x) (Producer a m x) (FreeT (Producer a' m) m x) (FreeT (Producer a m) m x)
wordsBy isWordSep k p0 = fmap concats (k (wordsBy' p0))
  where
    wordsBy' :: Monad m => Producer a' m r -> FreeT (Producer a' m) m r
    wordsBy' p =
      FreeT $ do
        x <- next p
        return $
          case x of
            Left r -> Pure r
            Right (a, p') ->
              Free $
              fmap
                wordsBy'
                (yield a >>
                 fmap (>-> Pipes.drop 1) (p' ^. Pipes.span (not . isWordSep)))

splitTest :: Foldl.Fold Text [Text]
splitTest = fmap (map Text.unlines . List.wordsBy (== "===")) Foldl.list

groupTests :: (Monad m) => Producer Text m () -> Producer [Text] m ()
groupTests p = Foldl.purely folds splitTest (p ^. wordsBy (== "---"))

withTestsFromFile :: FilePath -> (Int -> Text) -> ([Text] -> Expectation) -> Spec
withTestsFromFile path nameNthTest createTest = do
  tests <-
    (runIO . runSafeT . Pipes.toListM . groupTests) (Pipes.readFileLn path)
  zipWithM_
    (\test i -> it ((toS . nameNthTest) i) (createTest test))
    tests
    [1 ..]

shouldBeFile :: Text -> FilePath -> Expectation
shouldBeFile actual file = do
  expected <- liftIO (Text.readFile file)
  actual `shouldBe` expected
