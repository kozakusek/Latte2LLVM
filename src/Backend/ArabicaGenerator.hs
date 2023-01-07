{-# LANGUAGE LambdaCase #-}
module Backend.ArabicaGenerator where

import Backend.Milkremover
    ( Label,
      Method(retType, args, types, body),
      Espresso(Espresso),
      Value(VString, VInt, VBool),
      Instruction(..),
      ET(V, L),
      EspressoType(..) )
import qualified Data.Map as Map
import Data.List (intercalate, transpose)
import Control.Monad.State ( State, MonadState (get, put), evalState, foldM, mapAndUnzipM )
import Data.Maybe ( catMaybes, mapMaybe )

generateLLVM :: Espresso -> String
generateLLVM (Espresso functions) =
  let
    (strings, _) = foldr getStringsFromFun (Map.empty, 1) functions
    sm = Map.map (\id -> "@.str_" ++ show id) strings
  in unlines $ genLLVMstrings strings ++ "":runtimeDecls ++ "":genLLVMfunctions sm functions

genLLVMfunctions :: Map.Map String String -> Map.Map Label Method -> [String]
genLLVMfunctions sm fns =  genLLVMfunction sm <$> Map.toList fns

genLLVMfunction :: Map.Map String String -> (Label, Method) -> String
genLLVMfunction sm (label, method) =
  "define "
    ++ genType (retType method)
    ++ " @"
    ++ label
    ++ "("
    ++ intercalate ", " (getArgs method)
    ++ ") {\n"
    ++ "entry:\n"
    ++ unlines (genLLVMallocs method)
    ++ unlines (genLLVMargStores method)
    ++ "\n"
    ++ unlines (tail $ genLLVMbody sm method)
    ++ "  unreachable\n"
    ++ "}\n"

genLLVMallocs :: Method -> [String]
genLLVMallocs method = mapMaybe genLLVMalloc (Map.toList (types method))
  where
    genLLVMalloc (label, typ) = case typ of
      EI32 -> Just $ cmdPrefix ++ "%" ++ label ++ " = alloca i32"
      EI1 -> Just $cmdPrefix ++ "%" ++ label ++ " = alloca i1"
      EStr -> Just $ cmdPrefix ++ "%" ++ label ++ " = alloca i8*"
      EVoid -> Nothing

genLLVMargStores :: Method -> [String]
genLLVMargStores method = genLLVMargStore <$> args method
  where
    ts = types method
    genLLVMargStore label =
      cmdPrefix ++ "store " ++ genType typ ++ " %_" ++ label ++ ", " ++ genType typ ++ "* %" ++ label
      where
        typ = ts Map.! label

startsWith :: String -> [Char] -> Bool
startsWith pref str = pref == take (length pref) str

getArgs :: Method -> [String]
getArgs method = zipWith (\reg typ -> genType typ ++ " " ++ reg) registers ts
  where
    registers = ("%_" ++) <$> args method
    ts = (types method Map.!) <$> args method

type ArabicaBodyM = State Integer

getTemp :: ArabicaBodyM String
getTemp = do
  id <- get
  put (id + 1)
  return $ "t" ++ show id

genLLVMbody :: Map.Map String String -> Method -> [String]
genLLVMbody sm method = reverse $ evalState (genLLVMbody' bd) 0
  where
    bd = body method
    ts = types method
    genLLVMbody' = foldM aux []
      where
        aux acc instr = do
          llvmInstr <- genLLVMinstr sm ts instr
          return $ llvmInstr ++ acc

genLLVMinstr :: Map.Map String String -> Map.Map Label EspressoType -> Instruction -> ArabicaBodyM [String]
genLLVMinstr sm ts i = case i of
  ADD s et et' -> case ts Map.! s of
    EI1 -> error "ADD on bool"
    EI32 -> genSimpleInstr "i32" "i32" "add" s et et'
    EStr -> do
      t1 <- getTemp
      t2 <- getTemp
      t3 <- getTemp
      let (a1, l1) = getStrOp t1 et
      let (a2, l2) = getStrOp t2 et'
      return $ [
        cmdPrefix ++ "store i8* %" ++ t3 ++ ", i8** %" ++ s,
        cmdPrefix ++ "%" ++ t3 ++ " = call i8* @concatStrings(i8* " ++ a1 ++ ", i8* " ++ a2 ++ ")"
        ] ++ l1 ++ l2
    EVoid -> error "ADD on void"
  SUB s et et' -> genSimpleInstr "i32" "i32" "sub" s et et'
  MUL s et et' -> genSimpleInstr "i32" "i32" "mul" s et et'
  DIV s et et' -> genSimpleInstr "i32" "i32" "sdiv" s et et'
  MOD s et et' -> genSimpleInstr "i32" "i32" "srem" s et et'
  AND s et et' -> genSimpleInstr "i1" "i1" "and" s et et'
  OR s et et'  -> genSimpleInstr "i1" "i1" "or" s et et'
  EQS s et et' -> case getTypeEt et of
    EI1 -> genSimpleInstr "i1" "i1" "icmp eq" s et et'
    EI32 -> genSimpleInstr "i32" "i1" "icmp eq" s et et'
    EStr -> do
      t1 <- getTemp
      t2 <- getTemp
      t3 <- getTemp
      let (a1, l1) = getStrOp t1 et
      let (a2, l2) = getStrOp t2 et'
      return $ [
        cmdPrefix ++ "store i8* %" ++ t3 ++ ", i8** %" ++ s,
        cmdPrefix ++ "%" ++ t3 ++ " = call i1 @cmpstr(i8* " ++ a1 ++ ", i8* " ++ a2 ++ ")"
        ] ++ l1 ++ l2
    EVoid -> error "EQS on void"
  NEQ s et et' -> case getTypeEt et of
    EI1 -> genSimpleInstr "i1" "i1" "xor" s et et'
    EI32 -> genSimpleInstr "i32" "i1" "icmp ne" s et et'
    EStr -> do
      t1 <- getTemp
      t2 <- getTemp
      t3 <- getTemp
      t4 <- getTemp
      let (a1, l1) = getStrOp t1 et
      let (a2, l2) = getStrOp t2 et'
      return $ [
        cmdPrefix ++ "store i8* %" ++ t4 ++ ", i8** %" ++ s,
        cmdPrefix ++ "%" ++ t4 ++ " = xor i1 1, %" ++ t3,
        cmdPrefix ++ "%" ++ t3 ++ " = call i1 @cmpstr(i8* " ++ a1 ++ ", i8* " ++ a2 ++ ")"
        ] ++ l1 ++ l2
    EVoid -> error "NEQ on void"
  GRT s et et' -> genSimpleInstr "i32" "i1" "icmp sgt" s et et'
  GRE s et et' -> genSimpleInstr "i32" "i1" "icmp sge" s et et'
  LRT s et et' -> genSimpleInstr "i32" "i1" "icmp slt" s et et'
  LRE s et et' -> genSimpleInstr "i32" "i1" "icmp sle" s et et'
  NEG s et -> case et of
    L s' -> do
      t1 <- getTemp
      t2 <- getTemp
      return [
        cmdPrefix ++ "store i32 %" ++ t2 ++ ", i32* %" ++ s,
        cmdPrefix ++ "%" ++ t2 ++ " = sub i32 0, %" ++ t1,
        cmdPrefix ++ "%" ++ t1 ++ " = load i32, i32* %" ++ s'
        ]
    V (VInt i) -> return [cmdPrefix ++ "store i32 " ++ show (-i) ++ ", i32* %" ++ s]
    _ -> error "NEG: not an integer"
  NOT s et -> case et of
    L s' -> do
      t1 <- getTemp
      t2 <- getTemp
      return [
        cmdPrefix ++ "store i1 %" ++ t2 ++ ", i1* %" ++ s,
        cmdPrefix ++ "%" ++ t2 ++ " = xor i1 1, %" ++ t1,
        cmdPrefix ++ "%" ++ t1 ++ " = load i1, i1* %" ++ s'
        ]
    V (VBool b) -> return [cmdPrefix ++ "store i1 " ++ (if b then "0" else "1") ++ ", i1* %" ++ s]
    _ -> error "NOT: not a boolean"
  CPY s et -> case et of
    L s' -> do
      t <- getTemp
      return [
        cmdPrefix ++ "store " ++ genType (ts Map.! s') ++ " %" ++ t ++ ", " ++ genType (ts Map.! s') ++ "* %" ++ s,
        cmdPrefix ++ "%" ++ t ++ " = load " ++ genType (ts Map.! s') ++ ", " ++ genType (ts Map.! s') ++ "* %" ++ s'
        ]
    V (VInt n) -> return [cmdPrefix ++ "store i32 " ++ show n ++ ", i32* %" ++ s]
    V (VBool b) -> return [cmdPrefix ++ "store i1 " ++ (if b then "1" else "0") ++ ", i1* %" ++ s]
    V (VString str) -> do
      t <- getTemp
      return [
        cmdPrefix ++ "store i8* %" ++ t ++ ", i8** %" ++ s,
        cmdPrefix ++ "%" ++ t ++ " = getelementptr inbounds [" ++ show (length str + 1) ++ " x i8], ["
        ++ show (length str + 1) ++ " x i8]* " ++ sm Map.! str ++ ", i32 0, i32 0"
        ]
  CALL s f ets -> do
    t <- getTemp
    (args, maybeLoads) <- mapAndUnzipM (\case
          L s -> do
            t <- getTemp
            return (genType (ts Map.! s) ++ " %" ++ t, Just(
              cmdPrefix ++ "%" ++ t ++ " = load " ++ genType (ts Map.! s) ++ ", " ++ genType (ts Map.! s) ++ "* %" ++ s,
              "%" ++ t))
          V (VInt n) -> return ("i32 " ++ show n, Nothing)
          V (VBool b) -> return ("i1 " ++ (if b then "1" else "0"), Nothing)
          V (VString str) -> return ("i8* getelementptr inbounds ([" ++ show (length str + 1) ++ " x i8], ["
            ++ show (length str + 1) ++ " x i8]* " ++ sm Map.! str ++ ", i32 0, i32 0)",  Nothing)) ets
    let loads = map fst $  catMaybes maybeLoads
    case ts Map.! s of
      EVoid -> return $ (
          cmdPrefix ++ "call " ++ genType (ts Map.! s) ++ " @" ++ f ++ "(" ++ intercalate ", " args ++ ")") : loads
      _ -> return $ [
        cmdPrefix ++ "store " ++ genType (ts Map.! s) ++ " %" ++ t ++ ", " ++ genType (ts Map.! s) ++ "* %" ++ s,
        cmdPrefix ++ "%" ++ t ++ " = call " ++ genType (ts Map.! s) ++ " @" ++ f ++ "(" ++ intercalate ", " args ++ ")"
        ] ++ loads
  CBR et s1 s2 -> case et of
    L s -> do
      t <- getTemp
      return [
        cmdPrefix ++ "br i1 %" ++ t ++ ", label %" ++ s1 ++ ", label %" ++ s2,
        cmdPrefix ++ "%" ++ t ++ " = load i1, i1* %" ++ s
        ]
    V (VBool b) -> error "CBR: constant bool should have been optimized away"
    _ -> error "CBR: expected bool"
  BR s -> return [cmdPrefix ++ "br label %" ++ s]
  RET et -> case et of
    L s -> do
      t <- getTemp
      return [
        cmdPrefix ++ "ret " ++ genType (ts Map.! s) ++ " %" ++ t,
        cmdPrefix ++ "%" ++ t ++ " = load " ++ genType (ts Map.! s) ++ ", " ++ genType (ts Map.! s) ++ "* %" ++ s
        ]
    V (VInt n) ->  return [cmdPrefix ++ "ret i32 " ++ show n]
    V (VBool b) -> return [cmdPrefix ++ "ret i1 " ++ show b]
    V (VString s) -> return [
      cmdPrefix ++ "ret i8* getelementptr inbounds ([" ++ show (length s + 1) ++ " x i8], ["
      ++ show (length s) ++ " x i8]* " ++ sm Map.! s ++ ", i32 0, i32 0)"
      ]
  VRET -> return [cmdPrefix ++ "ret void"]
  LAB s -> return [s ++ ":"]
  where
    genSimpleInstr arg ret op s et et' = do
      t1 <- getTemp
      t2 <- getTemp
      t3 <- getTemp
      let (v1, l1) = case et of
            L s' -> ("%" ++ t1, [cmdPrefix ++ "%" ++ t1 ++ " = load " ++ arg ++ ", " ++ arg ++ "* %" ++ s'])
            V (VInt n) -> (show n, [])
            V (VBool b) -> (if b then "1" else "0", [])
            _ -> error "genSimpleInstr: not an integer"
      let (v2, l2) = case et' of
            L s' -> ("%" ++ t2, [cmdPrefix ++ "%" ++ t2 ++ " = load " ++ arg ++ ", " ++ arg ++ "* %" ++ s'])
            V (VInt n) -> (show n, [])
            V (VBool b) -> (if b then "1" else "0", [])
            _ -> error "genSimpleInstr: not an integer"
      return $ [
        cmdPrefix ++ "store " ++ ret ++ " %" ++ t3 ++ ", " ++ ret ++ "* %" ++ s,
        cmdPrefix ++ "%" ++ t3 ++ " = " ++ op ++ " " ++ arg ++ " " ++ v1 ++ ", " ++ v2
        ] ++ l1 ++ l2
    getStrOp t et = case et of
      L s -> ("%" ++ t, [cmdPrefix ++ "%" ++ t ++ " = load i8*, i8** %" ++ s])
      V (VString s') -> ("getelementptr inbounds (["
          ++ show (length s' + 1)
          ++ " x i8], ["
          ++ show (length s' + 1)
            ++ " x i8]* "
          ++ sm Map.! s'
          ++ ", i32 0, i32 0)", [])
      _ -> undefined
    getTypeEt et = case et of
      L s -> ts Map.! s
      V (VInt _) -> EI32
      V (VBool _) -> EI1
      V (VString _) -> EStr

genLLVMstrings :: Map.Map String Int -> [String]
genLLVMstrings = (defStr <$>) . Map.toList
  where
    defStr (str, id) =
      "@.str_"
        ++ show id
        ++ " = private constant ["
        ++ show (length str + 1)
        ++ " x i8] c\""
        ++ escapeString str
        ++ "\\00\""

escapeString :: String -> String
escapeString = concatMap escapeChar
  where
    escapeChar c = case c of
      '"' -> "\\22"
      '\\' -> "\\\\"
      '\a' -> "\\07"
      '\b' -> "\\08"
      '\f' -> "\\0C"
      '\n' -> "\\0A"
      '\r' -> "\\0D"
      '\t' -> "\\09"
      '\v' -> "\\0B"
      _ -> [c]

getStringsFromFun :: Method -> (Map.Map String Int, Int) -> (Map.Map String Int, Int)
getStringsFromFun method start = foldr aux start (body method)
  where
    addEtToMap et (m, id) = case et of
      V (VString s) -> (Map.insert s id m, id + 1)
      _ -> (m, id)
    aux instr (m, id) = case instr of
      ADD _ et et' -> (addEtToMap et . addEtToMap et') (m, id)
      EQS _ et et' -> (addEtToMap et . addEtToMap et') (m, id)
      NEQ _ et et' -> (addEtToMap et . addEtToMap et') (m, id)
      CPY _ et -> addEtToMap et (m, id)
      CALL _ str ets -> foldr addEtToMap (m, id) ets
      RET et -> addEtToMap et (m, id)
      _ -> (m, id)

runtimeDecls :: [String]
runtimeDecls = genRuntimeDecl <$> runtimeFunctions
  where
    genRuntimeDecl (name, args, ret) =
      "declare "
        ++ genType ret
        ++ " @"
        ++ name
        ++ "("
        ++ intercalate ", " (genType <$> args)
        ++ ")"

genType :: EspressoType -> String
genType EStr = "i8*"
genType EI1 = "i1"
genType EI32 = "i32"
genType EVoid = "void"

runtimeFunctions :: [(String, [EspressoType], EspressoType)]
runtimeFunctions = [
    ("concatStrings", [EStr, EStr], EStr),
    ("compareStrings", [EStr, EStr], EI1),
    ("printInt", [EI32], EVoid),
    ("printString", [EStr], EVoid),
    ("readInt", [], EI32),
    ("readString", [], EStr),
    ("error", [], EVoid)
  ]

cmdPrefix :: String
cmdPrefix = "  "