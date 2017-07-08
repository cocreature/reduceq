module Reduceq.Coq.TypingSpec
  ( typeInferenceSpec
  , withType
  ) where

import Reduceq.Prelude

import Test.Hspec

import Reduceq.Coq
import Reduceq.Imp.Parser

import Reduceq.Spec.Util

mkVar :: Word -> Ann () (Expr ())
mkVar id = Ann () (Var (VarId id Nothing))

ann :: Expr () -> Ann () (Expr ())
ann = Ann ()

int :: Integer -> Ann () (Expr ())
int = ann . IntLit

typeInferenceTests :: [(Expr (), Either InferError Ty)]
typeInferenceTests =
  [ (IntLit 1, Right TyInt)
  , (Abs TyInt Nothing (mkVar 0), Right (TyFun TyInt TyInt))
  , ( Abs
        TyInt
        Nothing
        (ann
           (Iter
              (ann
                 (Abs
                    TyInt
                    Nothing
                    (ann
                       (If
                          (ann (IntComp ILt (mkVar 0) (mkVar 1)))
                          (ann (Inr (ann (IntBinop IAdd (mkVar 0) (int 1)))))
                          (ann (Inl (ann Unit)))))))
              (ann (IntLit 0))))
    , Right (TyFun TyInt TyInt))
  , (Fst (int 1), Left (ExpectedProd TyInt))
  , (Inl (int 1), Left (AmbigousType "Cannot infer the type of `inl`."))
  , ( Abs (TyArr TyInt) Nothing (ann (Set (mkVar 0) (int 0) (int 0)))
    , Right (TyFun (TyArr TyInt) (TyArr TyInt)))
  , ( Abs (TyArr TyInt) Nothing (ann (Read (mkVar 0) (int 0)))
    , Right (TyFun (TyArr TyInt) TyInt))
  ]

testTypeInference :: Expr () -> Either InferError Ty -> Expectation
testTypeInference expr expectedTy =
  fmap (\(Ann ty _) -> ty) (runInferM (inferType expr)) `shouldBe` expectedTy

typeInferenceSpec :: SpecWith ()
typeInferenceSpec =
  describe "type inference" $ do
    mapM_
      (\(test, i) ->
         it
           ("infers type of example " <> show i <> " correctly")
           (uncurry testTypeInference test))
      (zip typeInferenceTests [(1 :: Int) ..])
    it "should preserve type of original program across transformation" $ do
      withParseResult fileParser "fn f(x : Int) -> [Int] { return 1; }" $ \decls ->
        withTransformed decls $ \transformed ->
          runInferM (inferType transformed) `shouldBe`
          Left (ErrorIn (IntLit 1) (TypeMismatch (TyArr TyInt) TyInt))
