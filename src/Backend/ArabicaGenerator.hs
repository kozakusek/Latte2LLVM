module Backend.ArabicaGenerator where

import Backend.Milkremover
  ( ClMap,
    Class (Class, fields, ordering, parent, methods),
    ET (L, V),
    Espresso (Espresso, classes),
    EspressoType (..),
    Instruction (..),
    Label,
    Method (args, body, retType, types),
    Value (VBool, VClass, VInt, VNull, VString), methodOwner,
  )
import Control.Monad.State (MonadState (get, put), State, evalState, foldM, mapAndUnzipM)
import Data.List (elemIndex, intercalate, transpose, sort)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromJust, mapMaybe)

lookupik m k = case Map.lookup k m of
  Just v -> v
  Nothing -> error $ "lookupik: " ++ show k ++ " not found in " ++ show m

generateLLVM :: Espresso -> String
generateLLVM (Espresso functions cls) =
  let (strings, _) = foldr getStringsFromFun (Map.empty, 1) functions
      sm = Map.map (\id -> "@.str_" ++ show id) strings
      (vtables, ordering) = unzip $ genVtables functions cls
      mo = Map.fromList ordering
   in unlines $
        genLLVMstrings strings
          ++ ""
          : vtables
          ++ ""
          : classDecls cls
          ++ ""
          : runtimeDecls
          ++ ""
          : genLLVMfunctions mo cls sm functions

classDecls :: ClMap -> [String]
classDecls cls = genClassDecl <$> Map.toList cls
  where
    genClassDecl (label, Class fields ordering _ _) =
      "%class." ++ label ++ " = type {\n  " ++ intercalate ",\n  " args ++ "\n}"
      where
        args = ("%" ++ label ++ "$vtable_type*") : (genType <$> ((fields Map.!) <$> ordering))


genVtables :: Map.Map Label Method -> ClMap -> [(String, (Label, [Label]))]
genVtables funs cls = genVtable <$> Map.keys cls
  where
    genVtable label = (vt ++ "\n" ++ vd, order)
      where
        vt = "%" ++ label ++ "$vtable_type = type {\n" ++ intercalate ",\n" vts ++ vts_  ++ "}"
        vd = "@" ++ label ++ "$vtable = global %" ++ label ++ "$vtable_type {\n" ++ intercalate ",\n" vds ++ vds_ ++ "}"
        vts = stringifyType label <$> meths
        vts_ = if null vts then "" else "\n"
        vds = stringify label <$> meths
        vds_ = if null vds then "" else "\n"
        meths = clMethods label
        order = (label, fst3 <$> meths)
    clMethods :: Label -> [(Label, EspressoType, [EspressoType])]
    clMethods name = parentMethods `joinMeth`  myMethods
      where
        parentMethods = maybe [] clMethods (parent (cls `lookupik` name))
        myMethods = map findMeth $ sort $ methods (cls `lookupik` name)
        findMeth :: Label -> (Label, EspressoType, [EspressoType])
        findMeth label = (label, retType fun, arglst)
          where
            fun = funs `lookupik` (name ++ "." ++ label)
            ts = types fun
            arglst = (ts `lookupik`) <$> args fun
        joinMeth p m = p ++ filter (\(l,_,_) -> l `notElem` (fst3 <$> p)) m
    stringifyType :: Label -> (Label, EspressoType, [EspressoType]) -> String
    stringifyType cl (mname, ret, argTypes) = cmdPrefix ++ genType ret ++ "(" ++ intercalate ", " args ++ ")*"
      where
        owner = fromJust $ methodOwner cls mname cl
        args = ("%class." ++ owner ++ "*") : (genType <$> drop 1 argTypes)
    stringify :: Label -> (Label, EspressoType, [EspressoType]) -> String
    stringify cl a@(mname, ret, argTypes) = stringifyType cl a ++ " @" ++ owner ++ "." ++ mname
      where
        owner = fromJust $ methodOwner cls mname cl

genLLVMfunctions :: Map.Map Label [Label] -> ClMap -> Map.Map String String -> Map.Map Label Method -> [String]
genLLVMfunctions mo cls sm fns = genLLVMfunction mo fns cls sm <$> Map.toList fns

genLLVMfunction :: Map.Map Label [Label] -> Map.Map Label Method -> ClMap -> Map.Map String String -> (Label, Method) -> String
genLLVMfunction mo fns cls sm (label, method) =
  "define "
    ++ genType (retType method)
    ++ " @"
    ++ label
    ++ "("
    ++ intercalate ", " (getArgs method)
    ++ ") {\n"
    ++ unlines (genLLVMbody mo fns cls sm method)
    ++ "}\n"

startsWith :: String -> [Char] -> Bool
startsWith pref str = pref == take (length pref) str

getArgs :: Method -> [String]
getArgs method = zipWith (\reg typ -> genType typ ++ " " ++ reg) registers ts
  where
    registers = ("%" ++) <$> args method
    ts = (types method `lookupik`) <$> args method

type ArabicaBodyM = State (Integer, Map.Map Label Method, Map.Map Label [Label])

getTemp :: ArabicaBodyM String
getTemp = do
  (id, fns, mo) <- get
  put (id + 1, fns, mo)
  return $ "t" ++ show id

getRetType :: Label -> ArabicaBodyM EspressoType
getRetType name = do
  (_, fns, _) <- get
  return $ retType (fns `lookupik` name)

getMethTypeS :: Label -> ArabicaBodyM String
getMethTypeS name = do
  (_, fns, _) <- get
  let f = fns `lookupik` name
  let ts = types f
  let r = genType $ retType f
  return $ r ++ "(" ++ intercalate ", " (genType <$> (lookupik ts <$> args f)) ++ ")*"

getMethPos :: Label -> Label -> ArabicaBodyM Int
getMethPos clname name = do
  (_, _, mo) <- get
  let meths = mo `lookupik` clname
  return $ fromJust $ elemIndex name meths

genLLVMbody :: Map.Map Label [Label] -> Map.Map Label Method -> ClMap -> Map.Map String String -> Method -> [String]
genLLVMbody mo fns cls sm method = reverse $ evalState (genLLVMbody' bd) (0, fns, mo)
  where
    bd = body method
    ts = types method
    rt = retType method
    genLLVMbody' = foldM aux []
      where
        aux acc instr = do
          llvmInstr <- genLLVMinstr cls sm ts rt instr
          return $ llvmInstr ++ acc

genLLVMinstr :: ClMap -> Map.Map String String -> Map.Map Label EspressoType -> EspressoType -> Instruction -> ArabicaBodyM [String]
genLLVMinstr cls sm ts rt i = case i of
  ADD s et et' -> case ts `lookupik` s of
    EI1 -> error "ADD on bool"
    EI32 -> return [cmdPrefix ++ "%" ++ s ++ " = add i32 " ++ showET et ++ ", " ++ showET et']
    EStr -> return [cmdPrefix ++ "%" ++ s ++ " = call i8* @concatStrings(i8* " ++ showET et ++ ", i8* " ++ showET et' ++ ")"]
    x -> error $ "ADD on " ++ show x
  SUB s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = sub i32 " ++ showET et ++ ", " ++ showET et']
  MUL s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = mul i32 " ++ showET et ++ ", " ++ showET et']
  DIV s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = sdiv i32 " ++ showET et ++ ", " ++ showET et']
  MOD s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = srem i32 " ++ showET et ++ ", " ++ showET et']
  AND s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = and i1 " ++ showET et ++ ", " ++ showET et']
  OR s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = or i1 " ++ showET et ++ ", " ++ showET et']
  EQS s et et' -> case getETType et of
    EI1 -> return [cmdPrefix ++ "%" ++ s ++ " = icmp eq i1 " ++ showET et ++ ", " ++ showET et']
    EI32 -> return [cmdPrefix ++ "%" ++ s ++ " = icmp eq i32 " ++ showET et ++ ", " ++ showET et']
    EStr -> return [cmdPrefix ++ "%" ++ s ++ " = call i1 @cmpstr(i8* " ++ showET et ++ ", i8* " ++ showET et' ++ ")"]
    EClass x -> return [cmdPrefix ++ "%" ++ s ++ " = icmp eq %class." ++ x ++ "* " ++ showET et ++ ", " ++ showET et']
    EVoid -> error "EQS on void"
  NEQ s et et' -> case getETType et of
    EI1 -> return [cmdPrefix ++ "%" ++ s ++ " = icmp ne i1 " ++ showET et ++ ", " ++ showET et']
    EI32 -> return [cmdPrefix ++ "%" ++ s ++ " = icmp ne i32 " ++ showET et ++ ", " ++ showET et']
    EStr -> do
      t1 <- getTemp
      return
        [ cmdPrefix ++ "%" ++ s ++ " = xor i1 1, %" ++ t1,
          cmdPrefix ++ "%" ++ t1 ++ " = call i1 @cmpstr(i8* " ++ showET et ++ ", i8* " ++ showET et' ++ ")"
        ]
    EClass x -> return [cmdPrefix ++ "%" ++ s ++ " = icmp ne %class." ++ x ++ "* " ++ showET et ++ ", " ++ showET et']
    EVoid -> error "NEQ on void"
  GRT s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = icmp sgt i32 " ++ showET et ++ ", " ++ showET et']
  GRE s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = icmp sge i32 " ++ showET et ++ ", " ++ showET et']
  LRT s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = icmp slt i32 " ++ showET et ++ ", " ++ showET et']
  LRE s et et' -> return [cmdPrefix ++ "%" ++ s ++ " = icmp sle i32 " ++ showET et ++ ", " ++ showET et']
  NEG s et -> return [cmdPrefix ++ "%" ++ s ++ " = sub i32 0, " ++ showET et] -- probably will not occur
  NOT s et -> return [cmdPrefix ++ "%" ++ s ++ " = xor i1 1, " ++ showET et] -- probably will not occur
  CPY s et -> error "CPY should not occur in SSA form"
  PHI s vls ->
    return
      [ cmdPrefix
          ++ "%"
          ++ s
          ++ " = phi "
          ++ genType (ts `lookupik` s)
          ++ " "
          ++ intercalate ", " (map (\(v, l) -> "[" ++ showET v ++ ", %" ++ l ++ "]") vls)
      ]
  CALL s f ets -> if isMethod f
    then do
      let (owner, _:mth) = break (== '.') f
      let self = head ets
      let selfType = getETType self
      let args = map (\x -> genType (getETType x) ++ " " ++ showET x) $ drop 1 ets
      vtPtr <- getTemp
      let getVtblPtr = cmdPrefix ++ "%" ++ vtPtr ++ " = getelementptr inbounds %" ++ show selfType ++ ", %" ++ show selfType ++ "* " ++ showET self ++ ", i32 0, i32 0"
      vt <- getTemp
      let EClass name = selfType
      let loadVtbl = cmdPrefix ++ "%" ++ vt ++ " = load %" ++ name ++ "$vtable_type*, %" ++ name ++ "$vtable_type** %" ++ vtPtr
      methPtr <- getTemp
      methPos <- getMethPos name mth
      let getMethPtr = cmdPrefix ++ "%" ++ methPtr ++ " = getelementptr inbounds %" ++ name ++ "$vtable_type, %" ++ name ++ "$vtable_type* %" ++ vt ++ ", i32 0, i32 " ++ show methPos
      casted <- getTemp
      let cast = cmdPrefix ++ "%" ++ casted ++ " = bitcast " ++ genType selfType ++ " %" ++ showET self ++ " to %class." ++ owner ++ "*"
      let args' = if name == owner then (genType selfType ++ " " ++ showET self) : args else (genType selfType ++ " %" ++ casted) : args
      meth <- getTemp
      methType <- getMethTypeS f
      methRet <- getRetType f
      let loadMeth = cmdPrefix ++ "%" ++ meth ++ " = load " ++ methType ++ ", " ++ methType ++ "* %" ++ methPtr
      let call = case methRet of
            EVoid -> cmdPrefix ++ "call void %" ++ meth ++ "(" ++ intercalate ", " args' ++ ")"
            _ -> cmdPrefix ++ "%" ++ s ++ " = call " ++ genType methRet ++ " %" ++ meth ++ "(" ++ intercalate ", " args' ++ ")"
      return $ call : ([cast | name /= owner]) ++ [loadMeth, getMethPtr, loadVtbl, getVtblPtr]
    else
      let args = map (\x -> genType (getETType x) ++ " " ++ showET x) ets
      in case ts `lookupik` s of
            EVoid -> return [cmdPrefix ++ "call void @" ++ f ++ "(" ++ intercalate ", " args ++ ")"]
            _ -> return [cmdPrefix ++ "%" ++ s ++ " = call " ++ genType (ts `lookupik` s) ++ " @" ++ f ++ "(" ++ intercalate ", " args ++ ")"]
  CBR et s1 s2 -> return [cmdPrefix ++ "br i1 " ++ showET et ++ ", label %" ++ s1 ++ ", label %" ++ s2]
  BR s -> return [cmdPrefix ++ "br label %" ++ s]
  RET et -> return [cmdPrefix ++ "ret " ++ genType rt ++ " " ++ showET et]
  VRET -> return [cmdPrefix ++ "ret void"]
  LAB s -> return [s ++ ":"]
  GET s et str -> do
    t <- getTemp
    let (EClass x) = getETType et
    let pos = show $ (1 +) $ fromJust $ elemIndex str $ ordering $ cls `lookupik` x
    let ty = genType $ fields (cls `lookupik` x) `lookupik` str
    return
      [ cmdPrefix ++ "%" ++ s ++ " = load " ++ ty ++ ", " ++ ty ++ "* %" ++ t,
        cmdPrefix ++ "%" ++ t ++ " = getelementptr inbounds %class." ++ x ++ ", %class." ++ x ++ "* " ++ showET et ++ ", i32 0, i32 " ++ pos
      ]
  SET et str et' -> do
    t <- getTemp
    let (EClass x) = getETType et
    let pos = show $ (1 +) $ fromJust $ elemIndex str $ ordering $ cls `lookupik` x
    let ty = genType (getETType et')
    return
      [ cmdPrefix ++ "store " ++ ty ++ " " ++ showET et' ++ ", " ++ ty ++ "* %" ++ t,
        cmdPrefix ++ "%" ++ t ++ " = getelementptr inbounds %class." ++ x ++ ", %class." ++ x ++ "* " ++ showET et ++ ", i32 0, i32 " ++ pos
      ]
  NEW s ty -> do
    t <- getTemp
    vt <- getTemp
    return
      [ cmdPrefix ++ "store %" ++ ty ++ "$vtable_type* @" ++ ty ++ "$vtable, %" ++ ty ++ "$vtable_type** %" ++ vt,
        cmdPrefix ++ "%" ++ vt ++ " = getelementptr inbounds %class." ++ ty ++ ", %class." ++ ty ++ "* %" ++ s ++ ", i32 0, i32 0",
        cmdPrefix ++ "%" ++ s ++ " = bitcast i8* %" ++ t ++ " to %class." ++ ty ++ "*",
        cmdPrefix ++ "%" ++ t ++ " = call i8* @__calloc__(i32 " ++ show (sizeOf ty) ++ ")"
      ]
  CAST s ty et ->
    return
      [ cmdPrefix ++ "%" ++ s ++ " = bitcast " ++ genType (getETType et) ++ " " ++ showET et ++ " to %class." ++ ty ++ "*"
      ]
  where
    getETType et = case et of
      L s -> ts `lookupik` s
      V (VInt _) -> EI32
      V (VBool _) -> EI1
      V (VString s') -> EStr
      V (VClass x) -> EClass x
      V (VNull x) -> EClass x
    showET et = case et of
      L s -> "%" ++ s
      V (VInt i) -> show i
      V (VBool b) -> if b then "1" else "0"
      V (VString s') ->
        "getelementptr inbounds (["
          ++ show (length s' + 1)
          ++ " x i8], ["
          ++ show (length s' + 1)
          ++ " x i8]* "
          ++ sm
          `lookupik` s'
          ++ ", i32 0, i32 0)"
      V (VClass x) -> error "Class is not showable this way"
      V (VNull x) -> "null"
    sizeOf ty = case cls `lookupik` ty of Class m _ _ _ -> 4 + 4 * Map.size m

isMethod :: Label -> Bool
isMethod = elem '.'

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
genType (EClass x) = "%class." ++ x ++ "*"

runtimeFunctions :: [(String, [EspressoType], EspressoType)]
runtimeFunctions =
  [ ("concatStrings", [EStr, EStr], EStr),
    ("compareStrings", [EStr, EStr], EI1),
    ("printInt", [EI32], EVoid),
    ("printString", [EStr], EVoid),
    ("readInt", [], EI32),
    ("readString", [], EStr),
    ("error", [], EVoid),
    ("__calloc__", [EI32], EStr)
  ]

cmdPrefix :: String
cmdPrefix = "  "

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a