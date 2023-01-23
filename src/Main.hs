{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.State (runStateT)
import Backend.Milkremover
import Frontend.Desugaring (desugar)
import Frontend.Typechecker (typeCheck)
import Latte.Par (myLexer, pProgram)
import Latte.Print (Print (prt), render)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Control.Monad (when, foldM_)
import System.FilePath (takeBaseName, replaceExtension)
import Data.Either (fromRight)
import Backend.ArabicaGenerator (generateLLVM)
import System.Process (system)
import qualified Data.Map as Map
import Backend.SingleShotAffogato

compileFile :: Bool -> FilePath -> IO ()
compileFile v f = readFile f >>= compile v f

compile :: Bool -> FilePath -> String -> IO ()
compile verbose fn code = do
  when verbose $ putStrLn "Parsing..."
  let parsed = pProgram $ myLexer code
  case parsed of
    Left err -> mainErr err
    Right _ -> when verbose $ putStrLn "Desugaring..."
  let desugared = parsed >>= desugar
  case desugared of
    Left err -> mainErr err
    Right c -> when verbose $
      saveFile (replaceExtension fn ".desugared") (render $ prt 0 c) >>
      putStrLn "TypeChecking..."
  let checked = desugared >>= typeCheck
  case checked of
    Left err -> mainErr err
    Right _ -> when verbose $ putStrLn "Removing milk..."
  hPutStrLn stderr "OK"
#if COMPILER
  let esp = removeMilk (fromRight undefined checked)
  --mapM_ uglyDebug $ Map.assocs $ functions esp
  when verbose $ saveFile (replaceExtension fn ".esp") (show esp)
  when verbose $ putStrLn "Optimizing..."
  let espOpt = makeAffogato esp
  when verbose $ saveFile (replaceExtension fn ".esp.ssa") (show espOpt)
  when verbose $ putStrLn "Generating LLVM..."
  let code = generateLLVM espOpt
  saveFile (replaceExtension fn ".ll") code
  system $ "llvm-link " ++ (if verbose then "-v " else "") ++ "-o " ++ (replaceExtension fn ".bc") ++ " " ++ (replaceExtension fn ".ll") ++ " " ++ "lib/runtime.bc"
  return ()
#endif

mainErr :: String -> IO b
mainErr err = hPutStrLn stderr "ERROR" >> hPutStrLn stderr err >> exitFailure

saveFile :: String -> String -> IO ()
saveFile f s = writeFile f s >> putStrLn ("Saved to " ++ f)

main :: IO ()
main = do
  args <- getArgs
  let verbose = "-v" `elem` args
  case filter (/= "-v") args of
    [] -> hPutStrLn stderr "Error: no input files" >> exitFailure
    files -> mapM_ (compileFile verbose) files


uglyDebug :: (String, Method) -> IO ()
uglyDebug (name, m) = do
     putStrLn name
     let cfg = makeCFG m
     let dom = computeDominators cfg
     let idom = computeImmediateDominators cfg dom
     let df = computeDominanceFrontier cfg idom
     let phi = placePhiNodes cfg df
     let m'body1 = linearizeCFG $ renameVariables phi
     let m'body2 = linearizeCFG $ caffeinePropagation $ renameVariables phi
     let m'body3 = linearizeCFG $ collectDirtyCups $ caffeinePropagation $ renameVariables phi
     let m'body4 = linearizeCFG $ cleanUpAfterDead $ removeDeadBlocks $ collectDirtyCups $ caffeinePropagation $ renameVariables phi
     let only = linearizeCFG $ coffeTamping $ renameVariables phi
     print cfg
     putStrLn "DOMINATORS:"
     print dom
     putStrLn "IMMEDIATE DOMINATORS:"
     print idom
     putStrLn "DOMINANCE FRONTIER:"
     print df
     putStrLn "PHI NODES:"
     print phi
     putStrLn "ESP:"
     putStrLn $ unlines $ show <$> m'body1
     putStrLn "ESP (after caffeine propagation):"
     putStrLn $ unlines $ show <$> m'body2
     putStrLn "ESP (after caffeine propagation and dirty cup collection):"
     putStrLn $ unlines $ show <$> m'body3
     putStrLn "ESP (after caffeine propagation, dirty cup collection and dead code removal):"
     putStrLn $ unlines $ show <$> m'body4
     putStrLn "ESP (after caffeine propagation, dirty cup collection, dead code removal and coffee tamping):"
     putStrLn $ unlines $ show <$> only