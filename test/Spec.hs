import           Reduceq.Prelude

import           Test.Hspec

import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import           Reduceq.AST as AST
import qualified Reduceq.CoqAST as CoqAST
import           Reduceq.Parser
import           Reduceq.Pretty
import           Reduceq.Transform

testParseFunction :: Text -> FunDecl -> Expectation
testParseFunction input result =
  case parseText fundeclParser mempty input of
    Success result' -> result' `shouldBe` result
    Failure errInfo ->
      (expectationFailure .
       flip Pretty.displayS mempty . Pretty.renderPretty 0.8 80 . _errDoc)
        errInfo

functionParseTests :: [(Text, FunDecl)]
functionParseTests =
  [ ( "fn f(x : Int) -> Int { return (x + 1); }"
    , FunctionDeclaration
        "f"
        [TypedVar "x" TyInt]
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

testTransform :: AST.FunDecl -> Text -> Expectation
testTransform original expected =
  displayDoc (pprintExpr (runTransformM (transformDecl original))) `shouldBe`
  expected

transformTests :: [(AST.FunDecl,Text)]
transformTests =
  [ ( AST.FunctionDeclaration
        "f"
        [AST.TypedVar "x" AST.TyInt, AST.TypedVar "y" AST.TyInt]
        AST.TyInt
        [AST.Return (AST.VarRef "x")]
    , "(fun _ : Int. (fun _ : Int. v1))")
  , ( AST.FunctionDeclaration
        "f"
        [AST.TypedVar "x" AST.TyInt, AST.TypedVar "y" AST.TyInt]
        AST.TyInt
        [AST.Return (AST.VarRef "y")]
    , "(fun _ : Int. (fun _ : Int. v0))")
  , ( AST.FunctionDeclaration
        "f"
        [AST.TypedVar "x" AST.TyInt, AST.TypedVar "y" AST.TyInt]
        AST.TyInt
        [ AST.Assgn
            (AST.VarLoc "x")
            (AST.IntBinop AST.IAdd (AST.VarRef "y") (AST.IntLit 1))
        , AST.Return (AST.VarRef "x")
        ]
    , "(fun _ : Int. (fun _ : Int. ((fun _ : Int. v0) (v0 + 1))))")
  , ( AST.FunctionDeclaration
        "f"
        [AST.TypedVar "x" AST.TyInt]
        AST.TyInt
        [ AST.If
            (AST.IntComp AST.ILt (AST.VarRef "x") (AST.IntLit 0))
            [AST.Assgn (AST.VarLoc "x") (AST.IntLit 0)]
            Nothing
        , AST.Return (AST.VarRef "x")
        ]
    , "(fun _ : Int. ((fun _ : Int. v0) (if (v0 < 0) ((fun _ : Int. v0) 0) v0)))")
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
         it ("transforms example " <> show i <> " correctly")
         (uncurry testTransform test))
      (zip transformTests [(1 :: Int) ..])

main :: IO ()
main = hspec $ do
  parserSpec
