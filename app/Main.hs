module Main where

import Reduceq.Prelude

import Data.Text.Prettyprint.Doc.Render.Terminal
import Reduceq.CoqAST
import Reduceq.CoqAST.Typing
import Reduceq.Parser hiding (Parser)
import Reduceq.Pretty as Pretty
import Reduceq.PrettyCoq as PrettyCoq
import Reduceq.Transform

import Options.Applicative hiding (Success, Failure)

data CliArgs = CliArgs
  { argInputFile :: !FilePath
  , argOutputFile :: !(Maybe FilePath)
  , argCoqFormat :: !Bool
  } deriving (Show, Eq, Ord)

argsParser :: Parser CliArgs
argsParser =
  CliArgs <$>
  strOption (short 'i' <> metavar "PATH" <> help "Path to the input file") <*>
  optional
    (strOption
       (short 'o' <> metavar "PATH" <>
        help "Path to the output file. Defaults to stdout")) <*>
  switch (long "coq" <> help "Use the output format required by Coq")

main :: IO ()
main = do
  CliArgs { argInputFile = inputPath
          , argOutputFile = outputPath
          , argCoqFormat = coqFormat
          } <- execParser cliArgs
  input <- readFile inputPath
  case parseText fileParser mempty input of
    Success decls -> do
      let transformed = runTransformM (transformDecls decls)
      case transformed of
        Left err -> hPutStrLn stderr (showTransformError err)
        Right transformed' ->
          let reduced = betaReduce transformed'
              pprinted
                | coqFormat = PrettyCoq.pprintExpr reduced
                | otherwise = runPprintM (Pretty.pprintExpr reduced)
              ty = runInferM (inferType reduced)
          in case ty of
               Left err -> do
                 hPutStrLn stderr (showInferError err)
               Right ty' ->
                 case outputPath of
                   Nothing -> do
                     putDoc pprinted
                     when
                       (not coqFormat)
                       (putDoc (" : " <> Pretty.pprintTy ty'))
                   Just file ->
                     writeFile
                       file
                       (Pretty.displayDoc (PrettyCoq.pprintExample reduced ty'))
    Failure errInfo -> hPutStrLn stderr (renderParseError errInfo)
  where
    cliArgs =
      info
        (argsParser <**> helper)
        (fullDesc <>
         progDesc "Proof the equivalence of imperative and MapReduce algorithms" <>
         header
           "reduceq - program equivalence for imperative and MapReduce algorithms")
