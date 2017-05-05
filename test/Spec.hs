import           Reduceq.Prelude

import           Test.Hspec

import           Reduceq.AST as AST
import           Reduceq.CoqAST (betaReduce)
import           Reduceq.Parser
import           Reduceq.Pretty
import           Reduceq.Transform

parseError :: ErrInfo -> Expectation
parseError = expectationFailure . toS . renderParseError

expectParseResult :: (Show a, Eq a) => Parser a -> Text -> a -> Expectation
expectParseResult parser input result =
  case parseText parser mempty input of
    Success result' -> result' `shouldBe` result
    Failure errInfo -> parseError errInfo

testParseFunction :: Text -> FunDecl -> Expectation
testParseFunction input result = expectParseResult fundeclParser input result

functionParseTests :: [(Text, FunDecl)]
functionParseTests =
  [ ( "fn f(x : Int) -> Int { return (x + 1); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        [Return (IntBinop IAdd (VarRef "x") (IntLit 1))])
  , ( "fn f(x : Int, y : Int) -> Int { return (x + 1); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt, TypedVar "y" TyInt]
        TyInt
        [Return (IntBinop IAdd (VarRef "x") (IntLit 1))])
  , ( "fn f (x : Int) -> Int { x := x + 1; return (x + 1); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        [ Assgn "x" (IntBinop IAdd (VarRef "x") (IntLit 1))
        , Return (IntBinop IAdd (VarRef "x") (IntLit 1))
        ])
  , ( "fn f (x : Int) -> Int { y : Int = x + 1; return (y); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        [ VarDecl (TypedVar "y" TyInt) (IntBinop IAdd (VarRef "x") (IntLit 1))
        , Return (VarRef "y")
        ])
  , ( "fn f (x : Int) -> Int { y : Int = 0; while (y < x) { y := y + 1; } return (y); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        [ VarDecl (TypedVar "y" TyInt) (IntLit 0)
        , While
            (IntComp ILt (VarRef "y") (VarRef "x"))
            [Assgn "y" (IntBinop IAdd (VarRef "y") (IntLit 1))]
        , Return (VarRef "y")
        ])
  , ( "fn f (x : Int) -> Int { if (x < 0) { x := 1; } if (x > 0) { x := 2; } else { x := 3; } return (x); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        [ If
            (IntComp ILt (VarRef "x") (IntLit 0))
            [Assgn "x" (IntLit 1)]
            Nothing
        , If
            (IntComp IGt (VarRef "x") (IntLit 0))
            [Assgn "x" (IntLit 2)]
            (Just [Assgn "x" (IntLit 3)])
        , Return (VarRef "x")
        ])
  , ( "fn f(x : [Int]) -> Int { x[0] := 1; return 42; }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" (TyArr TyInt)]
        TyInt
        [Assgn "x" (Set (VarRef "x") (IntLit 0) (IntLit 1)), Return (IntLit 42)])
  , ( "fn f(n : [Int]) -> Int {\n\
      \  n[0] := 1;\n\
      \  return n[0];\n\
      \}\n"
    , FunctionDeclaration
        "f"
        [TypedVar "n" (TyArr TyInt)]
        TyInt
        [ Assgn "n" (Set (VarRef "n") (IntLit 0) (IntLit 1))
        , Return (Read (VarRef "n") (IntLit 0))
        ])
  , ( "fn f () -> Int {\n\
     \  x : Int = g(1);\n\
     \  return g(x, 2, 3);\n\
     \}"
    , FunctionDeclaration
        "f"
        []
        TyInt
        [ VarDecl (TypedVar "x" TyInt) (Call (VarRef "g") [IntLit 1])
        , Return (Call (VarRef "g") [VarRef "x", IntLit 2, IntLit 3])
        ])
  ]

testTransform :: Text -> Text -> Expectation
testTransform original expected =
  case parseText fundeclParser mempty original of
    Success parsedOriginal ->
      case runTransformM (transformDecl parsedOriginal) of
        Left err -> expectationFailure (toS (showTransformError err))
        Right transformed ->
          (displayCompact . runPprintM . pprintExpr) transformed `shouldBe`
          expected
    Failure errInfo -> parseError errInfo

transformTests :: [(Text,Text)]
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
    , "((fun ▢ : Int. ((fun ▢ : Int. ((fun ▢ : Int. ((fun ▢ : Int * Int * Int. (((fst v0) + (fst (snd v0))) + (snd (snd v0)))) (if (v2 < 0) ((fun ▢ : Int. ((fun ▢ : Int. (v1, (v0, v2))) 43)) 42) ((fun ▢ : Int. (v3, (v2, v0))) 47)))) 3)) 2)) 1)")
  , ( "fn f(n : Int) -> Int { i : Int = 0; j : Int = 0; while (i < n) { i := i + 1; j := j + 1; } return (j); }"
    , "(fun ▢ : Int. ((fun ▢ : Int. ((fun ▢ : Int. ((fun ▢ : Int * Int. (snd v0)) (iter (fun ▢ : Int * Int. (if ((fst v0) < v3) ((fun ▢ : Int. ((fun ▢ : Int. (inr (v1, v0))) ((snd v1) + 1))) ((fst v0) + 1)) (inl ()))) (v1, v0)))) 0)) 0))")
  , ( "fn f(n : [Int]) -> Int {\n\
      \  n[0] := 1;\n\
      \  return n[0];\n\
      \}\n"
    , "(fun ▢ : [Int]. ((fun ▢ : [Int]. (read v0 0)) (set v0 0 1)))")
  ]

testReducedTransform :: Text -> Text -> Expectation
testReducedTransform original expected =
  case parseText fundeclParser mempty original of
    Success parsedOriginal ->
      case runTransformM (transformDecl parsedOriginal) of
        Left err -> expectationFailure (toS (showTransformError err))
        Right transformed ->
          (displayCompact . runPprintM . pprintExpr . betaReduce) transformed `shouldBe`
          expected
    Failure errInfo -> parseError errInfo

reducedTransformTests :: [(Text, Text)]
reducedTransformTests =
  [ ( "fn f(x : Int, y : Int) -> Int { return (x); }"
    , "(fun ▢ : Int. (fun ▢ : Int. v1))")
  , ( "fn f(x : Int, y : Int) -> Int { return (y); }"
    , "(fun ▢ : Int. (fun ▢ : Int. v0))")
  , ( "fn f(x : Int, y : Int) -> Int { x := y + 1; return (x); }"
    , "(fun ▢ : Int. (fun ▢ : Int. ((fun ▢ : Int. v0) (v0 + 1))))")
  , ( "fn f(x : Int) -> Int { if (x < 0) { x := 0; } return (x); }"
    , "(fun ▢ : Int. ((fun ▢ : Int. v0) (if (v0 < 0) 0 v0)))")
  , ( "fn f() -> Int { x : Int = 1; y : Int = 2; z : Int = 3; if (x < 0) { x := 42; y := 43; } else { z := 47; } return (x+y+z); }"
    , "((fun ▢ : Int * Int * Int. (((fst v0) + (fst (snd v0))) + (snd (snd v0)))) (if (1 < 0) (42, (43, 3)) (1, (2, 47))))")
  , ( "fn f(n : Int) -> Int { i : Int = 0; j : Int = 0; while (i < n) { i := i + 1; j := j + 1; } return (j); }"
    , "(fun ▢ : Int. ((fun ▢ : Int * Int. (snd v0)) (iter (fun ▢ : Int * Int. (if ((fst v0) < v1) ((fun ▢ : Int. ((fun ▢ : Int. (inr (v1, v0))) ((snd v1) + 1))) ((fst v0) + 1)) (inl ()))) (0, 0))))")
  , ( "fn f(n : [Int]) -> Int {\n\
      \  n[0] := 1;\n\
      \  return n[0];\n\
      \}\n"
    , "(fun ▢ : [Int]. ((fun ▢ : [Int]. (read v0 0)) (set v0 0 1)))")
  ]


parserSpec :: Spec
parserSpec = do
  describe "parse function" $ do
    mapM_
      (\(test, i) ->
         it
           ("parses example " <> show i <> " correctly")
           (uncurry testParseFunction test))
      (zip functionParseTests [(1 :: Int) ..])
  describe "transform" $ do
    mapM_
      (\(test, i) ->
         it
           ("transforms example " <> show i <> " correctly")
           (uncurry testTransform test))
      (zip transformTests [(1 :: Int) ..])
  describe "transform and reduce" $ do
    mapM_
      (\(test, i) ->
         it
           ("transforms and reduces example " <> show i <> " correctly")
           (uncurry testReducedTransform test))
      (zip reducedTransformTests [(1 :: Int) ..])

main :: IO ()
main = hspec $ do
  parserSpec
