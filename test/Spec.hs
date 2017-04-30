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
  ]

parserSpec :: Spec
parserSpec =
  describe "parse function" $ do
    it "parses functions correctly" $ do
      foldMap (uncurry testParseFunction) functionParseTests

main :: IO ()
main = hspec $ do
  parserSpec
