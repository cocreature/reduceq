module Main where

import           Reduceq.Prelude

import           Reduceq.CoqAST
import           Reduceq.Parser hiding (Parser)
import           Reduceq.Pretty
import           Reduceq.Transform

import           Options.Applicative hiding (Success, Failure)

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

withOutputHandle :: Maybe FilePath -> (Handle -> IO a) -> IO a
withOutputHandle Nothing f = f stdout
wtihOutputHandle (Just path) f = withFile path WriteMode f

main :: IO ()
main = do
  CliArgs {argInputFile = inputPath, argOutputFile = outputPath} <-
    execParser cliArgs
  input <- readFile inputPath
  case parseText fundeclParser mempty input of
    Success parsedInput -> do
      let transformed = runTransformM (transformDecl parsedInput)
          reduced = pprintExpr (betaReduce transformed)
      withOutputHandle outputPath $ \handle ->
        hPutStrLn handle (displayDoc reduced)
    Failure errInfo -> hPutStrLn stderr (renderParseError errInfo)
  where
    cliArgs =
      info
        (argsParser <**> helper)
        (fullDesc <>
         progDesc "Proof the equivalence of imperative and MapReduce algorithms" <>
         header
           "reduceq - program equivalence for imperative and MapReduce algorithms")
