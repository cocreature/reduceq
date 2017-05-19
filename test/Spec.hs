{-# LANGUAGE OverloadedLists #-}
import           Reduceq.Prelude

import           Test.Hspec

import           Reduceq.AST as AST
import           Reduceq.CoqAST (betaReduce)
import qualified Reduceq.CoqAST as CoqAST
import           Reduceq.Parser
import           Reduceq.Pretty
import qualified Reduceq.PrettyCoq as PrettyCoq
import           Reduceq.Transform

import           Reduceq.CoqAST.TypingSpec

parseError :: ErrInfo -> Expectation
parseError = expectationFailure . toS . renderParseError

withParseResult :: (Show a, Eq a) => Parser a -> Text -> (a -> Expectation) -> Expectation
withParseResult parser input cont =
  case parseText parser mempty input of
    Success result -> cont result
    Failure errInfo -> parseError errInfo

expectParseResult :: (Show a, Eq a) => Parser a -> Text -> a -> Expectation
expectParseResult parser input result =
  withParseResult parser input (`shouldBe` result)

testParseFunction :: Text -> FunDecl -> Expectation
testParseFunction input result = expectParseResult fundeclParser input result

functionParseTests :: [(Text, FunDecl)]
functionParseTests =
  [ ( "fn f(x : Int) -> Int { return (x + 1); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        (FunctionBody [Return (IntBinop IAdd (VarRef "x") (IntLit 1))]))
  , ( "fn f(x : Int, y : Int) -> Int { return (x + 1); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt, TypedVar "y" TyInt]
        TyInt
        (FunctionBody [Return (IntBinop IAdd (VarRef "x") (IntLit 1))]))
  , ( "fn f (x : Int) -> Int { x := x + 1; return (x + 1); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        (FunctionBody
           [ Assgn "x" (IntBinop IAdd (VarRef "x") (IntLit 1))
           , Return (IntBinop IAdd (VarRef "x") (IntLit 1))
           ]))
  , ( "fn f (x : Int) -> Int { y : Int = x + 1; return (y); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        (FunctionBody
           [ VarDecl
               (TypedVar "y" TyInt)
               (IntBinop IAdd (VarRef "x") (IntLit 1))
           , Return (VarRef "y")
           ]))
  , ( "fn f (x : Int) -> Int { y : Int = 0; while (y < x) { y := y + 1; } return (y); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        (FunctionBody
           [ VarDecl (TypedVar "y" TyInt) (IntLit 0)
           , While
               (IntComp ILt (VarRef "y") (VarRef "x"))
               [Assgn "y" (IntBinop IAdd (VarRef "y") (IntLit 1))]
           , Return (VarRef "y")
           ]))
  , ( "fn f (x : Int) -> Int { if (x < 0) { x := 1; } if (x > 0) { x := 2; } else { x := 3; } return (x); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
        TyInt
        (FunctionBody
           [ If
               (IntComp ILt (VarRef "x") (IntLit 0))
               [Assgn "x" (IntLit 1)]
               Nothing
           , If
               (IntComp IGt (VarRef "x") (IntLit 0))
               [Assgn "x" (IntLit 2)]
               (Just [Assgn "x" (IntLit 3)])
           , Return (VarRef "x")
           ]))
  , ( "fn f(x : [Int]) -> Int { x[0] := 1; return 42; }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" (TyArr TyInt)]
        TyInt
        (FunctionBody
           [ Assgn "x" (Set (VarRef "x") (IntLit 0) (IntLit 1))
           , Return (IntLit 42)
           ]))
  , ( "fn f(x : [Int * Int]) -> Int { x{0} := 1; return 42; }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" (TyArr (TyInt `TyProd` TyInt))]
        TyInt
        (FunctionBody
           [ Assgn "x" (SetAtKey (VarRef "x") (IntLit 0) (IntLit 1))
           , Return (IntLit 42)
           ]))
  , ( "fn f(n : [Int * Int]) -> Int {\n\
      \  n{0} := 1;\n\
      \  return n{0};\n\
      \}\n"
    , FunctionDeclaration
        "f"
        [TypedVar "n" (TyArr (TyInt `TyProd` TyInt))]
        TyInt
        (FunctionBody
           [ Assgn "n" (SetAtKey (VarRef "n") (IntLit 0) (IntLit 1))
           , Return (ReadAtKey (VarRef "n") (IntLit 0))
           ]))
  , ( "fn f(n : [Int]) -> Int {\n\
      \  n[0] := 1;\n\
      \  return n[0];\n\
      \}\n"
    , FunctionDeclaration
        "f"
        [TypedVar "n" (TyArr TyInt)]
        TyInt
        (FunctionBody
           [ Assgn "n" (Set (VarRef "n") (IntLit 0) (IntLit 1))
           , Return (Read (VarRef "n") (IntLit 0))
           ]))
  , ( "fn f () -> Int {\n\
      \  x : Int = g(1);\n\
      \  return g(x, 2, 3);\n\
      \}"
    , FunctionDeclaration
        "f"
        []
        TyInt
        (FunctionBody
           [ VarDecl (TypedVar "x" TyInt) (Call (VarRef "g") [IntLit 1])
           , Return (Call (VarRef "g") [VarRef "x", IntLit 2, IntLit 3])
           ]))
  , ( "extern fn f () -> Int {}"
    , FunctionDeclaration "f" [] TyInt ExternFunction)
  ]

withTransformed :: NonEmpty AST.FunDecl -> (CoqAST.Expr CoqAST.VarId -> Expectation) -> Expectation
withTransformed decls cont =
  case runTransformM (transformDecls decls) of
    Left err -> expectationFailure (toS (showTransformError err))
    Right transformed -> cont transformed

testTransform :: Text -> Text -> Expectation
testTransform original expected =
  withParseResult fileParser original $ \decls ->
    withTransformed decls $ \transformed ->
      (displayCompact . runPprintM . pprintExpr) transformed `shouldBe` expected

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
  , ( "fn f(n : [Int * Int]) -> Int {\n\
      \  n{0} := 1;\n\
      \  return n{0};\n\
      \}\n"
    , "(fun ▢ : [Int * Int]. ((fun ▢ : [Int * Int]. (read_at_key v0 0)) (set_at_key v0 0 1)))")
  ]

testReducedTransform :: Text -> Text -> Expectation
testReducedTransform original expected =
  withParseResult fileParser original $ \decls ->
    withTransformed decls $ \transformed ->
      (displayCompact . runPprintM . pprintExpr . betaReduce) transformed `shouldBe`
      expected

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
    , "((fun ▢ : Int → Int. ((fun ▢ : Int → Int → Int → Int. ((fun ▢ : Int. (((v1 3) 2) v0)) (v1 1))) (fun ▢ : Int. (fun ▢ : Int. (fun ▢ : Int. ((v2 + v1) + v0)))))) (fun ▢ : Int. v0))")
  , ( "extern fn f(x : Int) -> Int {}\
      \fn g(x : Int) -> Int {\
      \ return f(x);\
      \}"
    , "((fun ▢ : Int \8594 Int. (fun ▢ : Int. (v1 v0))) f)")
  ]


main :: IO ()
main =
  hspec $ do
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
    typeInferenceSpec
    coqProveSpec

testProveSpec :: Text -> Text -> Expectation
testProveSpec input output =
  withParseResult fileParser input $ \decls ->
    withTransformed decls $ \transformed ->
      let reduced = betaReduce transformed
      in withType reduced $ \ty ->
           displayCompact (PrettyCoq.pprintExample reduced ty) `shouldBe` output

coqProveTests :: [(Text, Text)]
coqProveTests =
  [ ( "fn f(x : Int) -> Int {\
      \  return x + 1;\
      \}"
    , "Require Import Term Typing.\n\
      \Definition example  := (tabs TInt (tint_binop Add (tvar 0) (tint 1))).\n\
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
      \            empty_ctx |-- example g \\in (TArrow TInt TInt).\n\
      \Proof. unfold example. repeat econstructor; eauto. Qed.\n")
  ]

coqProveSpec :: Spec
coqProveSpec =
  describe "generate example" $
  mapM_
    (\(test, i) ->
       it
         ("generate the correct Coq file for example " <> show i)
         (uncurry testProveSpec test))
    (zip coqProveTests [(1 :: Int) ..])
