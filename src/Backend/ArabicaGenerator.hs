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

lookupik m k = case Map.lookup k m of
  Just v -> v
  Nothing -> error $ "lookupik: " ++ show k ++ " not found in " ++ show m

generateLLVM :: Espresso -> String
generateLLVM (Espresso functions) =
  let
    (strings, _) = foldr getStringsFromFun (Map.empty, 1) functions
    sm = Map.map (\id -> "@.str_" ++ show id) strings
  in  unlines $ genLLVMstrings strings ++ "":runtimeDecls ++ "":genLLVMfunctions sm functions

genLLVMfunctions :: Map.Map String String -> Map.Map Label Method -> [String]
genLLVMfunctions sm fns = genLLVMfunction sm <$> Map.toList fns

genLLVMfunction :: Map.Map String String -> (Label, Method) -> String
genLLVMfunction sm (label, method) =
  "define "
    ++ genType (retType method)
    ++ " @"
    ++ label
    ++ "("
    ++ intercalate ", " (getArgs method)
    ++ ") {\n"
    ++ unlines (genLLVMbody sm method)
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
        typ = ts `lookupik` label

startsWith :: String -> [Char] -> Bool
startsWith pref str = pref == take (length pref) str

getArgs :: Method -> [String]
getArgs method = zipWith (\reg typ -> genType typ ++ " " ++ reg) registers ts
  where
    registers = ("%" ++) <$> args method
    ts = (types method `lookupik`) <$> args method

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
    rt = retType method
    genLLVMbody' = foldM aux []
      where
        aux acc instr = do
          llvmInstr <- genLLVMinstr sm ts rt instr
          return $ llvmInstr ++ acc

genLLVMinstr :: Map.Map String String -> Map.Map Label EspressoType -> EspressoType  -> Instruction -> ArabicaBodyM [String]
genLLVMinstr sm ts rt i = case i of
  ADD s et et' -> case ts `lookupik` s of
    EI1 -> error "ADD on bool"
    EI32 -> return [cmdPrefix ++ "%" ++ s ++ " = add i32 " ++ showET et ++ ", " ++ showET et']
    EStr -> return [cmdPrefix ++ "%" ++ s ++ " = call i8* @concatStrings(i8* " ++ showET et ++ ", i8* " ++ showET et' ++ ")"]
    EVoid -> error "ADD on void"
  SUB s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = sub i32 " ++ showET et ++ ", " ++ showET et']
  MUL s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = mul i32 " ++ showET et ++ ", " ++ showET et']
  DIV s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = sdiv i32 " ++ showET et ++ ", " ++ showET et']
  MOD s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = srem i32 " ++ showET et ++ ", " ++ showET et']
  AND s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = and i1 " ++ showET et ++ ", " ++ showET et']
  OR s et et'  -> return [cmdPrefix ++ "%" ++ s ++ " = or i1 " ++ showET et ++ ", " ++ showET et']
  EQS s et et' -> case getETType et of
    EI1 -> return [cmdPrefix ++ "%" ++ s ++ " = icmp eq i1 " ++ showET et ++ ", " ++ showET et']
    EI32 -> return [cmdPrefix ++ "%" ++ s ++ " = icmp eq i32 " ++ showET et ++ ", " ++ showET et']
    EStr -> return [cmdPrefix ++ "%" ++ s ++ " = call i1 @cmpstr(i8* " ++ showET et ++ ", i8* " ++ showET et' ++ ")"]
    EVoid -> error "EQS on void"
  NEQ s et et' -> case getETType et of
    EI1 -> return [cmdPrefix ++ "%" ++ s ++ " = icmp ne i1 " ++ showET et ++ ", " ++ showET et']
    EI32 -> return [cmdPrefix ++ "%" ++ s ++ " = icmp ne i32 " ++ showET et ++ ", " ++ showET et']
    EStr -> do
      t1 <- getTemp
      return [
        cmdPrefix ++ "%" ++ s ++ " = xor i1 1, %" ++ t1,
        cmdPrefix ++ "%" ++ t1 ++ " = call i1 @cmpstr(i8* " ++ showET et ++ ", i8* " ++ showET et' ++ ")"
        ]
    EVoid -> error "NEQ on void"
  GRT s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = icmp sgt i32 " ++ showET et ++ ", " ++ showET et']
  GRE s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = icmp sge i32 " ++ showET et ++ ", " ++ showET et']
  LRT s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = icmp slt i32 " ++ showET et ++ ", " ++ showET et']
  LRE s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = icmp sle i32 " ++ showET et ++ ", " ++ showET et']
  NEG s et -> return [cmdPrefix ++ "%" ++ s ++ " = sub i32 0, " ++ showET et] -- probably will not occur
  NOT s et -> return [cmdPrefix ++ "%" ++ s ++ " = xor i1 1, " ++ showET et] -- probably will not occur
  CPY s et -> error "CPY should not occur in SSA form"
  PHI s vls -> return [
    cmdPrefix ++ "%" ++ s ++ " = phi " ++ genType (ts `lookupik` s) ++ " "
      ++ intercalate ", " (map (\(v, l) -> "[" ++ showET v ++ ", %" ++ l ++ "]") vls)]
  CALL s f ets -> let args = map (\x -> genType (getETType x) ++ " " ++ showET x) ets in case ts `lookupik` s of
    EVoid -> return [cmdPrefix ++ "call void @" ++ f ++ "(" ++ intercalate ", " args ++ ")"]
    _ -> return [cmdPrefix ++ "%" ++ s ++ " = call " ++ genType (ts `lookupik` s) ++ " @" ++ f ++ "(" ++ intercalate ", " args ++ ")"]
  CBR et s1 s2 -> return [cmdPrefix ++ "br i1 " ++ showET et ++ ", label %" ++ s1 ++ ", label %" ++ s2]
  BR s -> return [cmdPrefix ++ "br label %" ++ s]
  RET et -> return [cmdPrefix ++ "ret " ++ genType rt ++ " " ++ showET et]
  VRET -> return [cmdPrefix ++ "ret void"]
  LAB s -> return [s ++ ":"]
  where
    getETType et = case et of
      L s -> ts `lookupik` s
      V (VInt _) -> EI32
      V (VBool _) -> EI1
      V (VString s') -> EStr
    showET et = case et of
      L s -> "%" ++ s
      V (VInt i) -> show i
      V (VBool b) -> if b then "1" else "0"
      V (VString s') -> "getelementptr inbounds (["
          ++ show (length s' + 1)
          ++ " x i8], ["
          ++ show (length s' + 1)
            ++ " x i8]* "
          ++ sm `lookupik` s'
          ++ ", i32 0, i32 0)"

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
      PHI _ vls -> foldr (\(v, _) -> addEtToMap v) (m, id) vls
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