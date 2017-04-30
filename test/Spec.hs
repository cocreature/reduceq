import           Reduceq.Prelude

import           Test.Hspec

import           Control.Lens
import           Reduceq.AST
import           Reduceq.Parser
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

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

parserSpec :: Spec
parserSpec =
  describe "parse function" $ do
    it "parses functions correctly" $ do
      foldMap (uncurry testParseFunction) functionParseTests

main :: IO ()
main = hspec $ do
  parserSpec
