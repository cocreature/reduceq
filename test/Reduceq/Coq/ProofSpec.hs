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
    mapM_
      (\(test, i) ->
         it
           ("generates the correct Coq file for example " <> show i)
           (uncurry testProofSingleSpec test))
      (zip coqProofSingleTests [(1 :: Int) ..])
  describe "generate proof obligation" $
    mapM_
      (\(test, i) ->
         it
           ("generates the correct Coq proof obligation for example " <> show i)
           (uncurry3 testProofSpec test))
      (zip coqProofTests [(1 :: Int) ..])

testProofSingleSpec :: Text -> Text -> Expectation
testProofSingleSpec input output =
  withParseResult fileParser input $ \decls ->
    withTransformed decls $ \transformed ->
      let reduced = betaReduce transformed
      in withType reduced $ \ty ->
           displayCompact (pprintExample reduced ty) `shouldBe` output

testProofSpec :: Text -> Text -> Text -> Expectation
testProofSpec imperativeInp mapreduceInp output =
  withTypedReduced imperativeInp $ \imperative imperativeTy ->
    withTypedReduced mapreduceInp $ \mapreduce mapreduceTy ->
      case (pprintProofObligation
              (imperative, imperativeTy)
              (mapreduce, mapreduceTy)) of
        Left err -> (expectationFailure . toS . showPprintError) err
        Right doc -> displayCompact doc `shouldBe` output

coqProofSingleTests :: [(Text, Text)]
coqProofSingleTests =
  [ ( "fn f(x : Int) -> Int {\
      \  return x + 1;\
      \}"
    , "Require Import Term Typing.\n\
      \Definition example := (tabs TInt (tint_binop Add (tvar 0) (tint 1))).\n\
      \Lemma example_typing :\n\
      \  empty_ctx |-- example \\in (TArrow TInt TInt).\n\
      \Proof. unfold example. repeat econstructor; eauto. Qed.\n")
  , ( "extern fn g(x : Int) -> Int {}\
      \fn f(x : Int) -> Int {\
      \ return g(x);\
      \}"
    , "Require Import Term Typing.\n\
      \Definition example g := (tapp (tabs (TArrow TInt TInt) (tabs TInt (tapp (tvar 1) (tvar 0)))) g).\n\
      \Lemma example_typing :\n\
      \  forall g, empty_ctx |-- g \\in (TArrow TInt TInt) ->\n\
      \       empty_ctx |-- example g \\in (TArrow TInt TInt).\n\
      \Proof. unfold example. repeat econstructor; eauto. Qed.\n")
  ]

coqProofTests :: [(Text, Text, Text)]
coqProofTests =
  [ ( "extern fn g(x : Int) -> Int {}\
      \fn f(x : Int) -> Int {\
      \  return g(x);\
      \}"
    , "extern fn g(x : Int) -> Int {}\
      \fn f(x : Int) -> Int {\
      \  return g(x);\
      \}"
    , "Require Import Step Term Typing.\n\
      \Definition imperative g := (tapp (tabs (TArrow TInt TInt) (tabs TInt (tapp (tvar 1) (tvar 0)))) g).\n\
      \Definition mapreduce g := (tapp (tabs (TArrow TInt TInt) (tabs TInt (tapp (tvar 1) (tvar 0)))) g).\n\
      \Lemma imperative_typing :\n\
      \  forall g, empty_ctx |-- g \\in (TArrow TInt TInt) ->\n\
      \       empty_ctx |-- imperative g \\in (TArrow TInt TInt).\n\
      \Proof. unfold imperative. repeat econstructor; eauto. Qed.\n\
      \Lemma mapreduce_typing :\n\
      \  forall g, empty_ctx |-- g \\in (TArrow TInt TInt) ->\n\
      \       empty_ctx |-- mapreduce g \\in (TArrow TInt TInt).\n\
      \Proof. unfold mapreduce. repeat econstructor; eauto. Qed.\n\
      \Lemma equivalence :\n\
      \  forall g, empty_ctx |-- g \\in (TArrow TInt TInt) ->\n\
      \       forall final,\n\
      \         bigstep (imperative g) final ->\n\
      \         bigstep (mapreduce g) final.\n\
      \Admitted.\n")
  ]
