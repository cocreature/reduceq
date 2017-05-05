module Main where

import Reduceq.Prelude

import Data.Text.Prettyprint.Doc.Render.Terminal
import Reduceq.CoqAST
import Reduceq.Parser hiding (Parser)
import Reduceq.Pretty
import Reduceq.Transform

import Options.Applicative hiding (Success, Failure)

data CliArgs = CliArgs
  { argInputFile :: !FilePath
  , argOutputFile :: !(Maybe FilePath)
  } deriving (Show, Eq, Ord)

argsParser :: Parser CliArgs
argsParser =
  CliArgs <$>
  strOption (short 'i' <> metavar "PATH" <> help "Path to the input file") <*>
  optional
    (strOption
       (short 'o' <> metavar "PATH" <>
        help "Path to the output file. Defaults to stdout"))

main :: IO ()
main = do
  CliArgs {argInputFile = inputPath, argOutputFile = outputPath} <-
    execParser cliArgs
  input <- readFile inputPath
  case parseText fileParser mempty input of
    Success decls -> do
      let transformed = runTransformM (transformDecls decls)
      case transformed of
        Left err -> hPutStrLn stderr (showTransformError err)
        Right transformed' ->
          let reduced = (runPprintM . pprintExpr . betaReduce) transformed'
          in case outputPath of
               Nothing ->
                 putDoc reduced
               Just file -> writeFile file (displayDoc reduced)
    Failure errInfo -> hPutStrLn stderr (renderParseError errInfo)
  where
    cliArgs =
      info
        (argsParser <**> helper)
        (fullDesc <>
         progDesc "Proof the equivalence of imperative and MapReduce algorithms" <>
         header
           "reduceq - program equivalence for imperative and MapReduce algorithms")
