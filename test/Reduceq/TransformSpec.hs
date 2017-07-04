module Reduceq.TransformSpec
  ( transformSpec
  , reducedTransformSpec
  ) where

import Reduceq.Prelude

import Test.Hspec

import Reduceq.Coq
import Reduceq.Imp

import Reduceq.Spec.Util

transformSpec :: Spec
transformSpec =
  describe "transform" $ do
    mapM_
      (\(test, i) ->
         it
           ("transforms example " <> show i <> " correctly")
           (uncurry testTransform test))
      (zip transformTests [(1 :: Int) ..])

reducedTransformSpec :: Spec
reducedTransformSpec =
  describe "transform and reduce" $ do
    mapM_
      (\(test, i) ->
         it
           ("transforms and reduces example " <> show i <> " correctly")
           (uncurry testReducedTransform test))
      (zip reducedTransformTests [(1 :: Int) ..])

testTransform :: Text -> Text -> Expectation
testTransform original expected =
  withParseResult fileParser original $ \decls ->
    withTransformed decls $ \transformed ->
      (displayCompact . runPprintM . pprintExpr) transformed `shouldBe` expected

testReducedTransform :: Text -> Text -> Expectation
testReducedTransform original expected =
  withParseResult fileParser original $ \decls ->
    withTransformed decls $ \transformed ->
      (displayCompact . runPprintM . pprintExpr . simplify) transformed `shouldBe`
      expected

transformTests :: [(Text, Text)]
transformTests =
  [ ( "fn f(x : Int, y : Int) -> Int { return (x); }"
    , "(fun ▢ : Int. (fun ▢ : Int. v1))")
  , ( "fn f(x : Int, y : Int) -> Int { return (y); }"
    , "(fun ▢ : Int. (fun ▢ : Int. v0))")
  , ( "fn f(x : Int, y : Int) -> Int { x := y + 1; return (x); }"
    , "(fun ▢ : Int. (fun ▢ : Int. ((fun ▢ : Int. v0) (v0 + 1))))")
  , ( "fn f(x : Int) -> Int { if (x < 0) { x := 0; } return (x); }"
    , "(fun ▢ : Int. ((fun ▢ : Int. v0) (if (v0 < 0) ((fun ▢ : Int. v0) 0) v0)))")
  , ( "fn f() -> Int { x : Int = 1; y : Int = 2; z : Int = 3; if (x < 0) { x := 42; y := 43; } else { z := 47; } return (x+y+z); }"
    , "((fun ▢ : Int. ((fun ▢ : Int. ((fun ▢ : Int. ((fun ▢ : (Int * (Int * Int)). (((fst v0) + (fst (snd v0))) + (snd (snd v0)))) (if (v2 < 0) ((fun ▢ : Int. ((fun ▢ : Int. (v1, (v0, v2))) 43)) 42) ((fun ▢ : Int. (v3, (v2, v0))) 47)))) 3)) 2)) 1)")
  , ( "fn f(n : Int) -> Int { i : Int = 0; j : Int = 0; while (i < n) { i := i + 1; j := j + 1; } return (j); }"
    , "(fun ▢ : Int. ((fun ▢ : Int. ((fun ▢ : Int. ((fun ▢ : (Int * Int). (snd v0)) (iter (fun ▢ : (Int * Int). (if ((fst v0) < v3) ((fun ▢ : Int. ((fun ▢ : Int. (inr (v1, v0))) ((snd v1) + 1))) ((fst v0) + 1)) (inl ()))) (v1, v0)))) 0)) 0))")
  , ( "fn f(n : [Int]) -> Int {\n\
      \  n[0] := 1;\n\
      \  return n[0];\n\
      \}\n"
    , "(fun ▢ : [Int]. ((fun ▢ : [Int]. (read v0 0)) (set v0 0 1)))")
  , ( "fn f(n : [(Int * Int)]) -> Int {\n\
      \  n{0} := 1;\n\
      \  return n{0};\n\
      \}\n"
    , "(fun ▢ : [(Int * Int)]. ((fun ▢ : [(Int * Int)]. (read_at_key v0 0)) (set_at_key v0 0 1)))")
  ]

reducedTransformTests :: [(Text, Text)]
reducedTransformTests =
  [ ( "fn f(x : Int, y : Int) -> Int { return (x); }"
    , "(fun ▢ : Int. (fun ▢ : Int. v1))")
  , ( "fn f(x : Int, y : Int) -> Int { return (y); }"
    , "(fun ▢ : Int. (fun ▢ : Int. v0))")
  , ( "fn f(x : Int, y : Int) -> Int { x := y + 1; return (x); }"
    , "(fun ▢ : Int. (fun ▢ : Int. (v0 + 1)))")
  , ( "fn f(x : Int) -> Int { if (x < 0) { x := 0; } return (x); }"
    , "(fun ▢ : Int. (if (v0 < 0) 0 v0))")
  , ( "fn f() -> Int { x : Int = 1; y : Int = 2; z : Int = 3; if (x < 0) { x := 42; y := 43; } else { z := 47; } return (x+y+z); }"
    , "((fun ▢ : (Int * (Int * Int)). (((fst v0) + (fst (snd v0))) + (snd (snd v0)))) (if (1 < 0) (42, (43, 3)) (1, (2, 47))))")
  , ( "fn f(n : Int) -> Int { i : Int = 0; j : Int = 0; while (i < n) { i := i + 1; j := j + 1; } return (j); }"
    , "(fun ▢ : Int. (snd (iter (fun \9634 : (Int * Int). (if ((fst v0) < v1) (inr (((fst v0) + 1), ((snd v0) + 1))) (inl ()))) (0, 0))))")
  , ( "fn f(n : [Int]) -> Int {\n\
      \  n[0] := 1;\n\
      \  return n[0];\n\
      \}\n"
    , "(fun \9634 : [Int]. (read (set v0 0 1) 0))")
  , ( "fn h(x : Int) -> Int {\
      \  return x;\
      \}\
      \fn g(x : Int, y : Int, z : Int) -> Int {\
      \  return x + y + z;\
      \}\
      \fn f () -> Int {\
      \  x : Int = h(1);\
      \  return g(x, 2, 3);\
      \}"
    , "((1 + 2) + 3)")
  , ( "extern fn f(x : Int) -> Int {}\
      \fn g(x : Int) -> Int {\
      \ return f(x);\
      \}"
    , "(fun \9634 : Int. (f v0))")
  , ( "extern fn splitWords(doc : Int) -> [Int] {}\
      \fn wordcount(docs : [Int]) -> [(Int * Int)] {\
      \  words : [Int] = flatMap((doc : Int) => splitWords(doc), docs);\
      \  wordTuples : [(Int * Int)] = map ((x : Int) => (x, 1), words);\
      \  return reduceByKey((x : Int) (y : Int) => x + y, 0, wordTuples);\
      \}"
    , "(fun \9634 : [Int]. (map (fun \9634 : (Int * [Int]). ((fst v0), (fold (fun \9634 : (Int * Int). ((fst v0) + (snd v0))) 0 (snd v0)))) (group (map (fun \9634 : Int. (v0, 1)) (concat (map (fun \9634 : Int. (splitWords v0)) v0))))))")
  , ( "fn wordcount(docs : [Int]) -> [(Int * Int)] {\
      \  map : [(Int * Int)] = [];\
      \  for ((doc : Int) : docs) {\
      \    map{doc} := 1;\
      \  }\
      \  return map;\
      \}"
    , "(fun ▢ : [Int]. (fold (fun ▢ : ([(Int * Int)] * Int). (set_at_key (fst v0) (snd v0) 1)) [] v0))")
  ]
