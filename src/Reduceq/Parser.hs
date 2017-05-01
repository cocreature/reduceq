{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Reduceq.Parser
  ( Parser
  , parseText
  , Result(..)
  , _Success
  , _errDoc
  , fundeclParser
  ) where

import           Reduceq.Prelude

import           Data.Char
import qualified Data.HashSet as HashSet
import           Data.Semigroup.Reducer
import           Text.Parser.Expression
import           Text.Parser.LookAhead (LookAheadParsing)
import           Text.Parser.Token.Highlight
import qualified Text.Trifecta as Trifecta
import           Text.Trifecta hiding (Parser)
import           Text.Trifecta.Delta (Delta(..))

import           Reduceq.AST

newtype Parser a =
  Parser (Trifecta.Parser a)
  deriving ( Functor
           , Applicative
           , Monad
           , Alternative
           , MonadPlus
           , Parsing
           , CharParsing
           , TokenParsing
           , LookAheadParsing
           , DeltaParsing
           , MarkParsing Delta
           )

newtype RopeText = RopeText { unRopeText :: Text }

instance Reducer RopeText Rope where
  unit = unit . strand . encodeUtf8 . unRopeText
  cons = cons . strand . encodeUtf8 . unRopeText
  snoc r = snoc r . strand . encodeUtf8 . unRopeText

parseText :: Parser a -> Delta -> Text -> Result a
parseText (Parser p) d inp = starve $ feed (RopeText inp) $ stepParser (release d *> p) mempty mempty

varId :: TokenParsing m => IdentifierStyle m
varId =
  IdentifierStyle
  { _styleName = "variable identifier"
  , _styleStart = lower
  , _styleLetter = alphaNum <|> oneOf "_'"
  , _styleReserved =
      HashSet.fromList ["fn", "for", "while", "if", "else", "elseif", "return"]
  , _styleHighlight = Identifier
  , _styleReservedHighlight = ReservedIdentifier
  }

funId :: TokenParsing m => IdentifierStyle m
funId =
  IdentifierStyle
  { _styleName = "function identifier"
  , _styleStart = lower
  , _styleLetter = alphaNum <|> oneOf "_'"
  , _styleReserved =
      HashSet.fromList ["fn", "for", "while", "if", "else", "elseif", "return"]
  , _styleHighlight = Identifier
  , _styleReservedHighlight = ReservedIdentifier
  }

varOp :: TokenParsing m => IdentifierStyle m
varOp =
  IdentifierStyle
  { _styleName = "variable operator"
  , _styleStart = oneOf "!#$%&*+./<=>?@\\^|-~" <|> satisfy isSymbol
  , _styleLetter = _styleStart varOp <|> char ':'
  , _styleReserved = HashSet.fromList ["=", "+", "-", "*", ",", ":="]
  , _styleHighlight = Operator
  , _styleReservedHighlight = ReservedOperator
  }

tyId :: TokenParsing m => IdentifierStyle m
tyId =
  IdentifierStyle
  { _styleName = "type identifier"
  , _styleStart = upper
  , _styleLetter = alphaNum
  , _styleReserved = HashSet.fromList ["Int"]
  , _styleHighlight = Identifier
  , _styleReservedHighlight = ReservedIdentifier
  }

tyParser :: Parser Ty
tyParser = TyInt <$ reserve tyId "Int"

tyVarParser :: Parser TypedVar
tyVarParser = do
  name <- ident varId
  _ <- colon
  ty <- tyParser
  pure (TypedVar name ty)

exprParser :: Parser Expr
exprParser = buildExpressionParser table term
  where
    term = choice [parens exprParser, VarRef <$> ident varId, IntLit <$> natural ]
    table =
      [ [intBinary "*" IMul]
      , [intBinary "+" IAdd, intBinary "-" ISub]
      , [intCompBinary "==" IEq, intCompBinary "<" ILt, intCompBinary ">" IGt]
      ]
    intBinary name op = Infix (IntBinop op <$ reserve varOp name) AssocLeft
    intCompBinary name op = Infix (IntComp op <$ reserve varOp name) AssocLeft

assgnLocParser :: Parser AssgnLocation
assgnLocParser = VarLoc <$> ident varId

backtrackingChoice :: [Parser a] -> Parser a
backtrackingChoice = choice . map try

stmtParser :: Parser Stmt
stmtParser =
  backtrackingChoice [while, ret, assgn, varDecl, if_] <?> "statement"
  where
    ret =
      (do reserve varId "return"
          expr <- parens exprParser
          _ <- semi
          pure (Return expr)) <?>
      "return statement"
    assgn =
      (do loc <- assgnLocParser
          reserve varOp ":="
          val <- exprParser
          _ <- semi
          pure (Assgn loc val)) <?>
      "assignment"
    varDecl =
      (do tyVar <- tyVarParser
          reserve varOp "="
          val <- exprParser
          _ <- semi
          pure (VarDecl tyVar val)) <?>
      "variable declaration"
    while =
      (do reserve varId "while"
          cond <- parens exprParser
          body <- braces (many stmtParser)
          pure (While cond body)) <?>
      "while loop"
    if_ =
      (do reserve varId "if"
          cond <- parens exprParser
          ifTrue <- braces (many stmtParser)
          ifFalse <- optional (reserve varId "else" *> braces (many stmtParser))
          pure (If cond ifTrue ifFalse)) <?>
      "if statement"

fundeclParser :: Parser FunDecl
fundeclParser =
  (do reserve funId "fn"
      name <- ident funId
      args <- parens (tyVarParser `sepBy` reserve varOp ",")
      _ <- token (text "->")
      returnTy <- tyParser
      body <- braces (many stmtParser)
      pure (FunctionDeclaration name args returnTy body)) <?>
  "function declaration"
