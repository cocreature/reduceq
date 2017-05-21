{-# LANGUAGE OverloadedLists #-}
module Reduceq.Imp.ParserSpec
  ( parserSpec
  ) where

import Reduceq.Prelude

import Test.Hspec

import Reduceq.Imp

import Reduceq.Spec.Util

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
  , ( "fn wordcount(docs : [Int]) -> [Int * Int] {\
      \  words : [Int] = flatMap((doc : Int) => splitWords(doc, docs));\
      \  wordTuples : [Int * Int] = map ((x : Int) => (x, 1));\
      \  return reduceByKey((x : Int) (y : Int) => x + y, wordTuples);\
      \}"
    , FunctionDeclaration
        "wordcount"
        [TypedVar "docs" (TyArr TyInt)]
        (TyArr (TyProd TyInt TyInt))
        (FunctionBody
           [ VarDecl
               (TypedVar "words" (TyArr TyInt))
               (Call
                  (VarRef "flatMap")
                  [ Lambda
                      [TypedVar "doc" TyInt]
                      (Call (VarRef "splitWords") [VarRef "doc", VarRef "docs"])
                  ])
           , VarDecl
               (TypedVar "wordTuples" (TyArr (TyProd TyInt TyInt)))
               (Call
                  (VarRef "map")
                  [Lambda [TypedVar "x" TyInt] (Pair (VarRef "x") (IntLit 1))])
           , Return
               (Call
                  (VarRef "reduceByKey")
                  [ Lambda
                      [TypedVar "x" TyInt, TypedVar "y" TyInt]
                      (IntBinop IAdd (VarRef "x") (VarRef "y"))
                  , VarRef "wordTuples"
                  ])
           ]))
  ]

parserSpec :: Spec
parserSpec =
  describe "parse function" $ do
    mapM_
      (\(test, i) ->
         it
           ("parses example " <> show i <> " correctly")
           (uncurry testParseFunction test))
      (zip functionParseTests [(1 :: Int) ..])
