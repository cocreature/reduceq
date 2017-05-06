module Reduceq.CoqAST.TypingSpec
  ( typeInferenceSpec
  ) where

import Reduceq.Prelude

import Test.Hspec

import Reduceq.CoqAST
import Reduceq.CoqAST.Typing

mkVar :: Word -> Expr VarId
mkVar = Var . VarId

typeInferenceTests :: [(Expr VarId, Either InferError Ty)]
typeInferenceTests =
  [ (IntLit 1, Right TyInt)
  , (Abs TyInt (mkVar 0), Right (TyFun TyInt TyInt))
  , ( Abs
        TyInt
        (Iter
           (Abs
              TyInt
              (If
                 (IntComp ILt (mkVar 0) (mkVar 1))
                 (Inr (IntBinop IAdd (mkVar 0) (IntLit 1)))
                 (Inl Unit)))
           (IntLit 0))
    , Right (TyFun TyInt TyInt))
  , (Fst (IntLit 1), Left (ExpectedProd TyInt))
  , (Inl (IntLit 1), Left (AmbigousType "Cannot infer the type of `inl`."))
  , ( Abs (TyArr TyInt) (Set (mkVar 0) (IntLit 0) (IntLit 0))
    , Right (TyFun (TyArr TyInt) (TyArr TyInt)))
  , ( Abs (TyArr TyInt) (Read (mkVar 0) (IntLit 0))
    , Right (TyFun (TyArr TyInt) TyInt))
  ]

testTypeInference :: Expr VarId
                  -> Either InferError Ty
                  -> Expectation
testTypeInference expr expectedTy =
  runInferM (inferType expr) `shouldBe` expectedTy

typeInferenceSpec :: SpecWith ()
typeInferenceSpec =
  describe "type inference" $ do
    mapM_
      (\(test, i) ->
         it
           ("infers type of example " <> show i <> " correctly")
           (uncurry testTypeInference test))
      (zip typeInferenceTests [(1 :: Int) ..])
