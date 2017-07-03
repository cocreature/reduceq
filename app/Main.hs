{-# LANGUAGE DuplicateRecordFields #-}
module Main where

import Reduceq.Prelude

import Control.Exception.Lens
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Reduceq.Coq
import Reduceq.Coq.Pretty as Pretty
import Reduceq.Imp.Parser hiding (Parser)
import Reduceq.Transform
import System.IO.Error.Lens

import Options.Applicative hiding (Success, Failure)

data DumpOptions = DumpOptions
  { optInputFile :: !FilePath
  } deriving (Show, Eq, Ord)

data ProveOptions = ProveOptions
  { optImperativeInputFile :: !FilePath
  , optMapReduceInputFile :: !FilePath
  , optOutputFile :: !(Maybe FilePath)
  } deriving (Show, Eq, Ord)

data ProveSingleOptions = ProveSingleOptions
  { optInputFile :: !FilePath
  , optOutputFile :: !(Maybe FilePath)
  } deriving (Show, Eq, Ord)

data ProveStepsOptions = ProveStepsOptions
  { optInputFile :: !FilePath
  , optOutputFile :: !(Maybe FilePath)
  } deriving (Show, Eq, Ord)

data Commands
  = DumpCommand !DumpOptions
  | ProveCommand !ProveOptions
  | ProveSingleCommand !ProveSingleOptions
  | ProveStepsCommand !ProveStepsOptions
  deriving (Show, Eq, Ord)

argsParser :: Parser Commands
argsParser =
  hsubparser
    (command
       "dump"
       (info
          (DumpCommand <$> dumpOptions)
          (progDesc
             "Dump the parsed representation and the inferred type to stdout")) <>
     command
       "prove"
       (info
          (ProveCommand <$> proveOptions)
          (progDesc "Generate a coq file including the proof obligation")) <>
     command
       "prove-single"
       (info
          (ProveSingleCommand <$> proveSingleOptions)
          (progDesc
             "Debugging command that generates a Coq file based on only a single input file")) <>
     command
       "steps"
       (info
          (ProveStepsCommand <$> proveStepsOptions)
          (progDesc
             "Generate a coq file based on the intermediate steps containing the proof obligations")))
  where
    dumpOptions = DumpOptions <$> strArgument (metavar "FILE")
    proveOptions =
      ProveOptions <$>
      strArgument (metavar "IMPERATIVE" <> help "Path to imperative algorithm") <*>
      strArgument (metavar "MAPREDUCE" <> help "Path to MapReduce algorithm") <*>
      optional (strOption (short 'o' <> metavar "FILE"))
    proveSingleOptions =
      ProveSingleOptions <$> strArgument (metavar "FILE") <*>
      optional (strOption (short 'o' <> metavar "FILE"))
    proveStepsOptions =
      ProveStepsOptions <$>
      strArgument (metavar "FILE" <> help "Path to input file") <*>
      optional
        (strOption
           (short 'o' <>
            (metavar "FILE" <>
             help "Path to generated Coq file. Defaults to stdout")))

withTypedReducedInputFile :: FilePath -> (Expr -> Ty -> IO ()) -> IO ()
withTypedReducedInputFile path cont = do
  input <- readFile path
  case parseText fileParser mempty input of
    Failure errInfo -> hPutStrLn stderr (renderParseError errInfo)
    Success decls ->
      case runTransformM (transformDecls decls) of
        Left err -> hPutStrLn stderr (showTransformError err)
        Right transformed ->
          let reduced = simplify (simplify transformed)
          in case runInferM (inferType reduced) of
               Left err -> hPutDoc stderr (showInferError err)
               Right ty -> cont reduced ty

dumpCommand :: DumpOptions -> IO ()
dumpCommand DumpOptions {optInputFile} =
  withTypedReducedInputFile optInputFile $ \reduced ty ->
    let pprinted = runPprintM (Pretty.pprintExpr reduced)
    in do putDoc pprinted
          putDoc (" : " <> Pretty.pprintTy ty)

proveCommand :: ProveOptions -> IO ()
proveCommand ProveOptions { optImperativeInputFile
                          , optMapReduceInputFile
                          , optOutputFile
                          } = do
  withTypedReducedInputFile optImperativeInputFile $ \imperative imperativeTy ->
    withTypedReducedInputFile optMapReduceInputFile $ \mapreduce mapreduceTy ->
      case pprintProofObligation
             (imperative, imperativeTy)
             (mapreduce, mapreduceTy) of
        Left err -> hPutStrLn stderr (showPprintError err)
        Right output' ->
          let output = Pretty.displayDoc output'
          in case optOutputFile of
               Nothing -> putStr output
               Just file -> writeFile file output

proveSingleCommand :: ProveSingleOptions -> IO ()
proveSingleCommand ProveSingleOptions {optInputFile, optOutputFile} = do
  withTypedReducedInputFile optInputFile $ \reduced ty ->
    let output = Pretty.displayDoc (pprintExample reduced ty)
    in case optOutputFile of
         Nothing -> putStrLn output
         Just file -> writeFile file output

handleNotExists :: FilePath -> IO a
handleNotExists path = do
  hPutDoc
    stderr
    (annotate
       (bold)
       (annotate (color Red) "Error" <> colon <+>
        "The file" <+> dquotes (pretty path) <+> "does not exist."))
  exitFailure

proveStepsCommand :: ProveStepsOptions -> IO ()
proveStepsCommand ProveStepsOptions {optInputFile, optOutputFile} = do
  input <-
    catching_
      (_IOException . errorType . _NoSuchThing)
      (readFile optInputFile)
      (handleNotExists optInputFile)
  case parseText stepsFileParser mempty input of
    Failure errInfo -> hPutStrLn stderr (renderParseError errInfo)
    Success steps -> do
      case runTransformM (transformProgramSteps steps) of
        Left err -> hPutStrLn stderr (showTransformError err)
        Right steps ->
          case runInferM (inferStepsType steps) of
            Left err -> hPutDoc stderr (showInferError err)
            Right ty ->
              case pprintProofStepsObligation (simplify <$> steps) ty of
                Left err -> hPutStrLn stderr (showPprintError err)
                Right doc ->
                  let output = Pretty.displayDoc doc
                  in case optOutputFile of
                       Nothing -> putStr output
                       Just file -> writeFile file output

main :: IO ()
main = do
  argCommand <- customExecParser (prefs showHelpOnEmpty) argsParserInfo
  case argCommand of
    DumpCommand opts -> dumpCommand opts
    ProveCommand opts -> proveCommand opts
    ProveSingleCommand opts -> proveSingleCommand opts
    ProveStepsCommand opts -> proveStepsCommand opts
  where
    argsParserInfo =
      info
        (argsParser <**> helper)
        (fullDesc <>
         progDesc "Proof the equivalence of imperative and MapReduce algorithms" <>
         header
           "reduceq - program equivalence for imperative and MapReduce algorithms")
