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
import Backend.SingleShotAffogato (makeCFG, computeDominators, computeImmediateDominators, computeDominanceFrontier, placePhiNodes)

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
  mapM_ (\(name, m) -> do
     putStrLn name
     let cfg = makeCFG m
     let dom = computeDominators cfg
     let idom = computeImmediateDominators cfg dom
     let df = computeDominanceFrontier cfg idom
     let phi = placePhiNodes cfg df
     putStrLn $ show $ cfg
     putStrLn "DOMINATORS:"
     putStrLn $ show $ dom 
     putStrLn "IMMEDIATE DOMINATORS:"
     putStrLn $ show $ idom
     putStrLn "DOMINANCE FRONTIER:"
     putStrLn $ show $ df
     putStrLn "PHI NODES:"
     putStrLn $ show $ phi
     ) $ Map.assocs $ functions esp
  when verbose $ saveFile (replaceExtension fn ".esp") (show esp)
  let code = generateLLVM esp
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
