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

instance Reducer Text Rope where
  unit = unit . strand . encodeUtf8
  cons = cons . strand . encodeUtf8
  snoc r = snoc r . strand . encodeUtf8

parseText :: Parser a -> Delta -> Text -> Result a
parseText (Parser p) d inp = starve $ feed inp $ stepParser (release d *> p) mempty mempty

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
  , _styleReserved = HashSet.fromList ["=", "+", "-", "*"]
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

intBinopParser :: Parser IntBinop
intBinopParser =
  choice
    [ IAdd <$ reserve varOp "+"
    , ISub <$ reserve varOp "-"
    , IMul <$ reserve varOp "*"
    ]

exprParser :: Parser Expr
exprParser = buildExpressionParser table term
  where
    term = choice [parens exprParser, VarRef <$> ident varId, IntLit <$> natural ]
    table =
      [ [intBinary "*" IMul AssocLeft]
      , [intBinary "+" IAdd AssocLeft, intBinary "-" ISub AssocLeft]
      ]
    intBinary name op assoc = Infix (IntBinop op <$ reserve varOp name) assoc

returnParser :: Parser Stmt
returnParser = do
  reserve varId "return"
  expr <- parens exprParser
  _ <- semi
  pure (Return expr)

stmtParser :: Parser Stmt
stmtParser = choice [returnParser]

fundeclParser :: Parser FunDecl
fundeclParser = do
  reserve funId "fn"
  name <- ident funId
  args <- parens (many tyVarParser)
  token (text "->")
  returnTy <- tyParser
  body <- braces (many stmtParser)
  pure (FunctionDeclaration name args returnTy body)
