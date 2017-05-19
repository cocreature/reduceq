{-# LANGUAGE MultiParamTypeClasses #-}
module Reduceq.Parser
  ( Parser
  , parseText
  , Result(..)
  , _Success
  , ErrInfo(..)
  , fileParser
  , fundeclParser
  , renderParseError
  ) where

import           Reduceq.Prelude

import           Data.Char
import qualified Data.HashSet as HashSet
import qualified Data.List.NonEmpty as NonEmpty
import           Data.Semigroup.Reducer
import           Text.Parser.Expression
import           Text.Parser.LookAhead (LookAheadParsing)
import           Text.Parser.Token.Highlight
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty
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
      HashSet.fromList
        ["fn", "for", "while", "if", "else", "elseif", "return", "extern"]
  , _styleHighlight = Identifier
  , _styleReservedHighlight = ReservedIdentifier
  }

identifier :: Parser VarId
identifier = ident varId

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

tyOp :: TokenParsing m => IdentifierStyle m
tyOp =
  IdentifierStyle
  { _styleName = "type operator"
  , _styleStart = oneOf ""
  , _styleLetter = oneOf ""
  , _styleReserved = HashSet.fromList ["*", "+"]
  , _styleHighlight = Operator
  , _styleReservedHighlight = ReservedOperator
  }

tyParser :: Parser Ty
tyParser = buildExpressionParser table term
  where
    term =
      choice
        [ parens tyParser
        , TyInt <$ reserve tyId "Int"
        , TyArr <$> brackets tyParser
        ]
    table = [[tyBinary "*" TyProd]]
    tyBinary name op = Infix (op <$ reserve tyOp name) AssocLeft

tyVarParser :: Parser TypedVar
tyVarParser = do
  name <- identifier
  _ <- colon
  ty <- tyParser
  pure (TypedVar name ty)

exprParser :: Parser Expr
exprParser = buildExpressionParser table term
  where
    term = choice [parens exprParser, VarRef <$> identifier, IntLit <$> natural]
    table =
      [ [Postfix arrayRead, Postfix mapRead, Postfix functionCall]
      , [intBinary "*" IMul]
      , [intBinary "+" IAdd, intBinary "-" ISub]
      , [intCompBinary "==" IEq, intCompBinary "<" ILt, intCompBinary ">" IGt]
      ]
    intBinary name op = Infix (IntBinop op <$ reserve varOp name) AssocLeft
    intCompBinary name op = Infix (IntComp op <$ reserve varOp name) AssocLeft
    arrayRead = do
      index <- brackets exprParser
      pure (\arr -> Read arr index)
    mapRead = do
      key <- braces exprParser
      pure (\arr -> ReadAtKey arr key)
    functionCall = do
      args <- NonEmpty.fromList <$> parens (exprParser `sepBy1` comma)
      pure (\name -> Call name args)

-- | This is only used in the parser. We transform assignments to an
-- array element to assignments to the array itself via set operations
-- so the final AST only contains assignments to variable identifiers.
data AssgnLocation
  = VarLoc !VarId
  | ArrLoc !VarId
           !Expr
  | MapLoc !VarId
           !Expr
  deriving (Show, Eq, Ord)

assgnLocParser :: Parser AssgnLocation
assgnLocParser = do
  name <- identifier
  index <-
    optional (Left <$> brackets exprParser <|> Right <$> braces exprParser)
  case index of
    Nothing -> pure (VarLoc name)
    Just (Left i) -> pure (ArrLoc name i)
    Just (Right key) -> pure (MapLoc name key)

stmtParser :: Parser Stmt
stmtParser = choice [while, ret, if_, varDecl, assgn] <?> "statement"
  where
    ret =
      (do reserve varId "return"
          expr <- exprParser
          _ <- semi
          pure (Return expr)) <?>
      "return statement"
    assgn =
      (do loc <- assgnLocParser
          reserve varOp ":="
          val <- exprParser
          _ <- semi
          case loc of
            VarLoc id -> pure (Assgn id val)
            ArrLoc id index -> pure (Assgn id (Set (VarRef id) index val))
            MapLoc id key -> pure (Assgn id (SetAtKey (VarRef id) key val))) <?>
      "assignment"
    varDecl =
      (do tyVar <- try tyVarParser
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
  (do extern <- isJust <$> optional (reserve varId "extern")
      reserve varId "fn"
      name <- identifier
      args <- parens (tyVarParser `sepBy` reserve varOp ",")
      _ <- token (text "->")
      returnTy <- tyParser
      body <-
        if extern
          then ExternFunction <$ braces (spaces)
          else FunctionBody <$> braces (some stmtParser)
      pure (FunctionDeclaration name args returnTy body)) <?>
  "function declaration"

fileParser :: Parser (NonEmpty FunDecl)
fileParser = some1 fundeclParser <* eof

renderParseError :: ErrInfo -> Text
renderParseError =
  toS . flip Pretty.displayS mempty . Pretty.renderPretty 0.8 80 . _errDoc
