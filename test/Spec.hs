import           Reduceq.Prelude

import           Test.Hspec
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import           Reduceq.AST as AST
import           Reduceq.CoqAST (betaReduce)
import           Reduceq.Parser
import           Reduceq.Pretty
import           Reduceq.Transform

parseError :: ErrInfo -> Expectation
parseError = expectationFailure . flip Pretty.displayS mempty . Pretty.renderPretty 0.8 80 . _errDoc

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
        [Return (IntBinop IAdd (VarRef (mkVarId "x")) (IntLit 1))])
  , ( "fn f(x : Int, y : Int) -> Int { return (x + 1); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt, TypedVar "y" TyInt]
        TyInt
        [Return (IntBinop IAdd (VarRef (mkVarId "x")) (IntLit 1))])
  , ( "fn f (x : Int) -> Int { x := x + 1; return (x + 1); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        [ Assgn (VarLoc "x") (IntBinop IAdd (VarRef "x") (IntLit 1))
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
            [Assgn (VarLoc "y") (IntBinop IAdd (VarRef "y") (IntLit 1))]
        , Return (VarRef "y")
        ])
  , ( "fn f (x : Int) -> Int { if (x < 0) { x := 1; } if (x > 0) { x := 2; } else { x := 3; } return (x); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        [ If
            (IntComp ILt (VarRef "x") (IntLit 0))
            [Assgn (VarLoc "x") (IntLit 1)]
            Nothing
        , If
            (IntComp IGt (VarRef "x") (IntLit 0))
            [Assgn (VarLoc "x") (IntLit 2)]
            (Just [Assgn (VarLoc "x") (IntLit 3)])
        , Return (VarRef "x")
        ])
  ]

testTransform :: Text -> Text -> Expectation
testTransform original expected =
  case parseText fundeclParser mempty original of
    Success parsedOriginal ->
      displayDoc (pprintExpr (runTransformM (transformDecl parsedOriginal))) `shouldBe`
      expected
    Failure errInfo -> parseError errInfo

transformTests :: [(Text,Text)]
transformTests =
  [ ( "fn f(x : Int, y : Int) -> Int { return (x); }"
    , "(fun _ : Int. (fun _ : Int. v1))")
  , ( "fn f(x : Int, y : Int) -> Int { return (y); }"
    , "(fun _ : Int. (fun _ : Int. v0))")
  , ( "fn f(x : Int, y : Int) -> Int { x := y + 1; return (x); }"
    , "(fun _ : Int. (fun _ : Int. ((fun _ : Int. v0) (v0 + 1))))")
  , ( "fn f(x : Int) -> Int { if (x < 0) { x := 0; } return (x); }"
    , "(fun _ : Int. ((fun _ : Int. v0) (if (v0 < 0) ((fun _ : Int. v0) 0) v0)))")
  , ( "fn f() -> Int { x : Int = 1; y : Int = 2; z : Int = 3; if (x < 0) { x := 42; y := 43; } else { z := 47; } return (x+y+z); }"
    , "((fun _ : Int. ((fun _ : Int. ((fun _ : Int. ((fun _ : Int * Int * Int. (((fst v0) + (fst (snd v0))) + (snd (snd v0)))) (if (v2 < 0) ((fun _ : Int. ((fun _ : Int. (v1, (v0, v2))) 43)) 42) ((fun _ : Int. (v3, (v2, v0))) 47)))) 3)) 2)) 1)")
  , ( "fn f(n : Int) -> Int { i : Int = 0; j : Int = 0; while (i < n) { i := i + 1; j := j + 1; } return (j); }"
    , "(fun _ : Int. ((fun _ : Int. ((fun _ : Int. ((fun _ : Int * Int. (snd v0)) (iter (fun _ : Int * Int. (if ((fst v0) < v3) ((fun _ : Int. ((fun _ : Int. (inr (v1, v0))) ((snd v1) + 1))) ((fst v0) + 1)) (inl ()))) (v1, v0)))) 0)) 0))")
  ]

testReducedTransform :: Text -> Text -> Expectation
testReducedTransform original expected =
  case parseText fundeclParser mempty original of
    Success parsedOriginal ->
      displayDoc
        (pprintExpr (betaReduce (runTransformM (transformDecl parsedOriginal)))) `shouldBe`
      expected
    Failure errInfo -> parseError errInfo

reducedTransformTests :: [(Text, Text)]
reducedTransformTests =
  [ ( "fn f(x : Int, y : Int) -> Int { return (x); }"
    , "(fun _ : Int. (fun _ : Int. v1))")
  , ( "fn f(x : Int, y : Int) -> Int { return (y); }"
    , "(fun _ : Int. (fun _ : Int. v0))")
  , ( "fn f(x : Int, y : Int) -> Int { x := y + 1; return (x); }"
    , "(fun _ : Int. (fun _ : Int. ((fun _ : Int. v0) (v0 + 1))))")
  , ( "fn f(x : Int) -> Int { if (x < 0) { x := 0; } return (x); }"
    , "(fun _ : Int. ((fun _ : Int. v0) (if (v0 < 0) 0 v0)))")
  , ( "fn f() -> Int { x : Int = 1; y : Int = 2; z : Int = 3; if (x < 0) { x := 42; y := 43; } else { z := 47; } return (x+y+z); }"
    , "((fun _ : Int * Int * Int. (((fst v0) + (fst (snd v0))) + (snd (snd v0)))) (if (1 < 0) (42, (43, 3)) (1, (2, 47))))")
  , ( "fn f(n : Int) -> Int { i : Int = 0; j : Int = 0; while (i < n) { i := i + 1; j := j + 1; } return (j); }"
    , "(fun _ : Int. ((fun _ : Int * Int. (snd v0)) (iter (fun _ : Int * Int. (if ((fst v0) < v1) ((fun _ : Int. ((fun _ : Int. (inr (v1, v0))) ((snd v1) + 1))) ((fst v0) + 1)) (inl ()))) (0, 0))))")
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
