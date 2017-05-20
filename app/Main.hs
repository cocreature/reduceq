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

data ProveOptions = ProveOptions
  { proveOptInputFile :: !FilePath
  , proveOptOutputFile :: !(Maybe FilePath)
  } deriving (Show, Eq, Ord)

data DumpOptions = DumpOptions
  { dumpOptInputFile :: !FilePath
  } deriving (Show, Eq, Ord)

data Commands
  = DumpCommand !DumpOptions
  | ProveCommand !ProveOptions
  deriving (Show, Eq, Ord)

argsParser :: Parser Commands
argsParser =
  subparser
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
          (progDesc "Generate a coq file including the proof obligation")))
  where
    dumpOptions = DumpOptions <$> strArgument (metavar "FILE")
    proveOptions =
      ProveOptions <$> strArgument (metavar "FILE") <*>
      optional (strOption (short 'o' <> metavar "FILE"))

withTypedReducedInputFile :: FilePath -> (Expr VarId -> Ty -> IO ()) -> IO ()
withTypedReducedInputFile path cont = do
  input <- readFile path
  case parseText fileParser mempty input of
    Failure errInfo -> hPutStrLn stderr (renderParseError errInfo)
    Success decls ->
      case runTransformM (transformDecls decls) of
        Left err -> hPutStrLn stderr (showTransformError err)
        Right transformed ->
          let reduced = betaReduce transformed
          in case runInferM (inferType reduced) of
               Left err -> hPutStrLn stderr (showInferError err)
               Right ty -> cont reduced ty

dumpCommand :: DumpOptions -> IO ()
dumpCommand DumpOptions {dumpOptInputFile} =
  withTypedReducedInputFile dumpOptInputFile $ \reduced ty ->
    let pprinted = runPprintM (Pretty.pprintExpr reduced)
    in do putDoc pprinted
          putDoc (" : " <> Pretty.pprintTy ty)

proveCommand :: ProveOptions -> IO ()
proveCommand ProveOptions {proveOptInputFile, proveOptOutputFile} = do
  withTypedReducedInputFile proveOptInputFile $ \reduced ty ->
    let output = Pretty.displayDoc (PrettyCoq.pprintExample reduced ty)
    in case proveOptOutputFile of
         Nothing -> putStrLn output
         Just file -> writeFile file output

main :: IO ()
main = do
  argCommand <- execParser argsParserInfo
  case argCommand of
    DumpCommand opts -> dumpCommand opts
    ProveCommand opts -> proveCommand opts
  where
    argsParserInfo =
      info
        (argsParser <**> helper)
        (fullDesc <>
         progDesc "Proof the equivalence of imperative and MapReduce algorithms" <>
         header
           "reduceq - program equivalence for imperative and MapReduce algorithms")
