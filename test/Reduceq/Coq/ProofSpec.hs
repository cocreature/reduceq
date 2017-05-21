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
           displayDoc (pprintExample reduced ty) `shouldBe` output

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
    , "Require Import Coq.Lists.List.\n\
      \Import ListNotations.\n\
      \Require Import Term Typing.\n\
      \Definition example :=\n\
      \  (tabs TInt (tint_binop Add (tvar 0) (tint 1))).\n\
      \Lemma example_typing :\n\
      \  empty_ctx |-- example \\in (TArrow TInt TInt).\n\
      \Proof. unfold example. repeat econstructor; eauto. Qed.\n")
  , ( "extern fn g(x : Int) -> Int {}\
      \fn f(x : Int) -> Int {\
      \ return g(x);\
      \}"
    , "Require Import Coq.Lists.List.\n\
      \Import ListNotations.\n\
      \Require Import Term Typing.\n\
      \Definition example g :=\n\
      \  (tapp (tabs (TArrow TInt TInt)\n\
      \              (tabs TInt (tapp (tvar 1) (tvar 0))))\n\
      \        g).\n\
      \Lemma example_typing :\n\
      \  forall g, empty_ctx |-- g \\in (TArrow TInt TInt) ->\n\
      \       empty_ctx |-- example g \\in (TArrow TInt TInt).\n\
      \Proof. unfold example. repeat econstructor; eauto. Qed.\n")
  , ( "extern fn splitWords(doc : Int) -> [Int] {}\n\
      \fn wordcount(docs : [Int]) -> [Int * Int] {\n\
      \  words : [Int] = flatMap((doc : Int) => splitWords(doc), docs);\n\
      \  wordTuples : [Int * Int] = map ((x : Int) => (x, 1), words);\n\
      \  return reduceByKey((x : Int) (y : Int) => x + y, 0, wordTuples);\n\
      \}"
    , "Require Import Coq.Lists.List.\n\
      \Import ListNotations.\n\
      \Require Import Term Typing.\n\
      \Definition example splitWords :=\n\
      \  (tapp (tabs (TArrow TInt (TList Local TInt))\n\
      \              (tabs (TList Local TInt)\n\
      \                    (tapp (tabs (TList Local TInt)\n\
      \                                (tapp (tabs (TList Local (TProd  TInt TInt))\n\
      \                                            (tmap (tabs (TProd  TInt (TList Local TInt))\n\
      \                                                        (tpair (tfst (tvar 0)) (tfold (tabs (TProd  TInt TInt)\n\
      \                                                                                            (tint_binop Add (tfst (tvar 0)) (tsnd (tvar 0))))\n\
      \                                                                                      (tint 0)\n\
      \                                                                                      (tsnd (tvar 0)))))\n\
      \                                                  (tgroup (tvar 0))))\n\
      \                                      (tmap (tabs TInt\n\
      \                                                  (tpair (tvar 0) (tint 1)))\n\
      \                                            (tvar 0))))\n\
      \                          (tconcat (tmap (tabs TInt (tapp (tvar 2) (tvar 0)))\n\
      \                                         (tvar 0))))))\n\
      \        splitWords).\n\
      \Lemma example_typing :\n\
      \  forall splitWords, empty_ctx |-- splitWords \\in (TArrow TInt\n\
      \                                                     (TList Local TInt)) ->\n\
      \                empty_ctx |-- example splitWords \\in (TArrow (TList Local TInt)\n\
      \                                                             (TList Local (TProd  TInt TInt))).\n\
      \Proof. unfold example. repeat econstructor; eauto. Qed.\n")
  , ( "extern fn splitWords(doc : Int) -> [Int] {}\n\
      \fn wordcount(docs : [Int]) -> [Int * Int] {\n\
      \  map : [Int * Int] = [];\n\
      \  for ((doc : Int) : docs) {\n\
      \    words : [Int] = splitWords(doc);\n\
      \    for ((word : Int) : words) {\n\
      \      match map{word} with\n\
      \      | l : () => { map{word} := 1; }\n\
      \      | r : Int => { map{word} := r + 1; }\n\
      \      end\n\
      \    }\n\
      \  }\n\
      \  return map;\n\
      \}\n"
    , "Require Import Coq.Lists.List.\n\
      \Import ListNotations.\n\
      \Require Import Term Typing.\n\
      \Definition example splitWords :=\n\
      \  (tapp (tabs (TArrow TInt (TList Local TInt))\n\
      \              (tabs (TList Local TInt)\n\
      \                    (tapp (tabs (TList Local (TProd  TInt TInt))\n\
      \                                (tfold (tabs (TProd  (TList Local (TProd  TInt TInt)) TInt)\n\
      \                                             (tapp (tabs (TList Local TInt)\n\
      \                                                         (tfold (tabs (TProd  (TList Local (TProd  TInt TInt)) TInt)\n\
      \                                                                      (tcase (tread_at_key (tsnd (tvar 0))\n\
      \                                                                                           (tfst (tvar 0))) (tset_at_key (tsnd (tvar 1))\n\
      \                                                                                                                         (tint 1)\n\
      \                                                                                                                         (tfst (tvar 1))) (tset_at_key (tsnd (tvar 1))\n\
      \                                                                                                                                                       (tint_binop Add (tvar 0) (tint 1))\n\
      \                                                                                                                                                       (tfst (tvar 1)))))\n\
      \                                                                (tfst (tvar 1))\n\
      \                                                                (tvar 0)))\n\
      \                                                   (tapp (tvar 3)\n\
      \                                                         (tsnd (tvar 0)))))\n\
      \                                       (tvar 0)\n\
      \                                       (tvar 1)))\n\
      \                          (tlist []))))\n\
      \        splitWords).\n\
      \Lemma example_typing :\n\
      \  forall splitWords, empty_ctx |-- splitWords \\in (TArrow TInt\n\
      \                                                     (TList Local TInt)) ->\n\
      \                empty_ctx |-- example splitWords \\in (TArrow (TList Local TInt)\n\
      \                                                             (TList Local (TProd  TInt TInt))).\n\
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
