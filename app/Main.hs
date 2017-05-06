module Main where

import Reduceq.Prelude

import Data.Text.Prettyprint.Doc.Render.Terminal
import Reduceq.CoqAST
import Reduceq.CoqAST.Typing
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
          let reduced = betaReduce transformed'
              pprinted = runPprintM (pprintExpr reduced)
              ty = runInferM (inferType reduced)
          in case outputPath of
               Nothing -> do
                 putDoc pprinted
                 case ty of
                   Left err -> do
                     hPutStrLn stderr (showInferError err)
                   Right ty' -> putDoc (" : " <> pprintTy ty')
               Just file -> writeFile file (displayDoc pprinted)
    Failure errInfo -> hPutStrLn stderr (renderParseError errInfo)
  where
    cliArgs =
      info
        (argsParser <**> helper)
        (fullDesc <>
         progDesc "Proof the equivalence of imperative and MapReduce algorithms" <>
         header
           "reduceq - program equivalence for imperative and MapReduce algorithms")
