{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}
module Backend.Milkremover where

import Control.Monad (foldM_, mapAndUnzipM, void, when)
import Control.Monad.Identity (Identity)
import Control.Monad.State (State, StateT, evalState, foldM, forM, get, put, replicateM)
import Data.List (elemIndex, foldl', sort, find)
import Data.Map (member)
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe, isNothing)
import qualified Frontend.Typechecker as FT
import Latte.Abs

lookupik m k = case Map.lookup k m of
  Just v -> v
  Nothing -> error $ "lookupik: " ++ show k ++ " not found in " ++ show m

type Label = String

data Value
  = VInt Integer
  | VBool Bool
  | VString String
  | VClass String
  | VNull String
  deriving (Eq, Ord)

espTrue, espFalse :: Value
espTrue = VBool True
espFalse = VBool False

data ET = L Label | V Value deriving (Eq, Ord)

data Instruction
  = ADD Label ET ET
  | SUB Label ET ET
  | MUL Label ET ET
  | DIV Label ET ET
  | MOD Label ET ET
  | AND Label ET ET
  | OR Label ET ET
  | EQS Label ET ET
  | NEQ Label ET ET
  | GRT Label ET ET
  | GRE Label ET ET
  | LRT Label ET ET
  | LRE Label ET ET
  | NEG Label ET
  | NOT Label ET
  | CPY Label ET
  | PHI Label [(ET, Label)]
  | CALL Label Label [ET]
  | CBR ET Label Label
  | BR Label
  | RET ET
  | VRET
  | LAB Label
  | GET Label ET Label
  | SET ET Label ET
  | NEW Label Label
  | CAST Label Label ET
  deriving (Eq, Ord)


type EspressoBlock = [Instruction]

data EspressoType = EI1 | EI32 | EStr | EVoid | EClass String

type ETypeMap = Map.Map Label EspressoType

type ClMap = Map.Map Label Class

data Method = Method
  { args :: [Label],
    body :: EspressoBlock,
    types :: ETypeMap,
    retType :: EspressoType
  }

data Class = Class {
  fields :: Map.Map Label EspressoType,
  ordering :: [Label],
  parent :: Maybe Label,
  methods :: [Label]
}

data Espresso = Espresso
  { functions :: Map.Map Label Method,
    classes :: Map.Map Label Class
  }

instance Show Value where
  show (VInt i) = show i
  show (VString s) = show s
  show (VBool b) = show b
  show (VClass n) = n ++ "(?)"
  show (VNull x) = "null(" ++ x ++ ")"


instance Show ET where
  show (L l) = l
  show (V v) = show v

instance Show Instruction where
  show (ADD l lv1 lv2) = l ++ " = " ++ show lv1 ++ " + " ++ show lv2
  show (SUB l lv1 lv2) = l ++ " = " ++ show lv1 ++ " - " ++ show lv2
  show (MUL l lv1 lv2) = l ++ " = " ++ show lv1 ++ " * " ++ show lv2
  show (DIV l lv1 lv2) = l ++ " = " ++ show lv1 ++ " / " ++ show lv2
  show (MOD l lv1 lv2) = l ++ " = " ++ show lv1 ++ " % " ++ show lv2
  show (AND l lv1 lv2) = l ++ " = " ++ show lv1 ++ " && " ++ show lv2
  show (OR l lv1 lv2) = l ++ " = " ++ show lv1 ++ " || " ++ show lv2
  show (EQS l lv1 lv2) = l ++ " = (" ++ show lv1 ++ " == " ++ show lv2 ++ ")"
  show (NEQ l lv1 lv2) = l ++ " = (" ++ show lv1 ++ " != " ++ show lv2 ++ ")"
  show (GRT l lv1 lv2) = l ++ " = (" ++ show lv1 ++ " > " ++ show lv2 ++ ")"
  show (GRE l lv1 lv2) = l ++ " = (" ++ show lv1 ++ " >= " ++ show lv2 ++ ")"
  show (LRT l lv1 lv2) = l ++ " = (" ++ show lv1 ++ " < " ++ show lv2 ++ ")"
  show (LRE l lv1 lv2) = l ++ " = (" ++ show lv1 ++ " <= " ++ show lv2 ++ ")"
  show (NEG l lv) = l ++ " = -" ++ show lv
  show (NOT l lv) = l ++ " = !" ++ show lv
  show (CPY l lv) = l ++ " = " ++ show lv
  show (PHI l lvs) = l ++ " = phi(" ++ unwords (map (\(l1, l2) -> "[" ++ show l1 ++ ", " ++ l2 ++ "]") lvs) ++ ")"
  show (CALL l1 l2 i) = l1 ++ " = call " ++ l2 ++ "(" ++ unwords (map show i) ++ ")"
  show (CBR v lv1 lv2) = "if " ++ show v ++ " goto " ++ lv1 ++ " else goto " ++ lv2
  show (BR l) = "goto " ++ l
  show (RET lv) = "return " ++ show lv
  show VRET = "return void"
  show (LAB l) = l ++ ":"
  show (GET l1 l2 l3) = l1 ++ " = (" ++ show l2 ++ ")." ++ l3
  show (SET l1 l2 l3) = "(" ++ show l1 ++ ")." ++ l2 ++ " = " ++ show l3
  show (NEW l1 l2) = l1 ++ " = new " ++ l2
  show (CAST l1 l2 l3) = l1 ++ " = (" ++ l2 ++ ") " ++ show l3

instance Show Class where
  show (Class fields ordering _ _) = "class {\n" ++
    unlines (map (\l -> "\t" ++ l ++ " : " ++ show (fields Map.! l)) ordering) ++
    "}\n"

instance Show Method where
  show (Method args body ts t) =
    show t ++ " fn(args = " ++ show ((\l -> (l, ts Map.! l)) <$> args) ++ ") {\n" ++ unlines (("\t" ++) . show <$> body) ++ "}\n"

instance Show Espresso where
  show (Espresso functions classes) =
    unlines (map (\(n, c) -> n ++ " = " ++ show c) (Map.toList classes)) ++
    "\n" ++
    unlines (map (\(n, f) -> n ++ " = " ++ show f) $ Map.toList functions)

instance Show EspressoType where
  show EI1 = "i1"
  show EI32 = "i32"
  show EStr = "str"
  show EVoid = "void"
  show (EClass n) = "class." ++ n

type LabMap = Map.Map Ident Label

type EspM = State (LabMap, Integer, Map.Map String EspressoType, Maybe Label)

freshLabel :: EspM Label
freshLabel = do
  (m, i, fr, cl) <- get
  put (m, i + 1, fr, cl)
  return $ show i

freshTmp :: EspM Label
freshTmp = do
  (m, i, fr, cl) <- get
  put (m, i + 1, fr, cl)
  return $ "e_" ++ show i

getLabMap :: EspM LabMap
getLabMap = do
  (m, i, fr, cl) <- get
  return m

putLabMap :: LabMap -> EspM ()
putLabMap m = do
  (m', i, fr, cl) <- get
  put (m, i, fr, cl)

getFunRetType :: String -> EspM EspressoType
getFunRetType f = do
  (m, i, fr, cl) <- get
  case fr Map.!? f of
    Just t -> return t
    Nothing -> return $ demilkType $ FT.methodRetType $ FT.builtinMethods `lookupik` Ident f

getClass :: EspM (Maybe Label)
getClass = do
  (m, i, fr, cl) <- get
  return cl

userLabel :: Label -> Ident -> Label
userLabel id (Ident x) = "u_" ++ id ++ "_" ++ x

removeMilk :: FT.Env -> Espresso
removeMilk env = Espresso {functions = demilkFunctions classes' env', classes = classes'}
  where
    classes' = demilkClasses env
    env' = addMethodsToEnv env
    addMethodsToEnv :: FT.Env -> FT.Env
    addMethodsToEnv env = env {FT.envFunctions = Map.union (FT.envFunctions env) methods}
      where
        methods = foldl Map.union Map.empty mms
        mms :: [Map.Map Ident FT.Method]
        mms = map modClMethods $ Map.assocs $ FT.envClasses env
        modClMethods :: (Ident, FT.Class) -> Map.Map Ident FT.Method
        modClMethods (Ident n, c) = modArgs $ modNames $ modKeys $ FT.classMethods c
          where
            modKeys = Map.mapKeys (\(Ident x) -> Ident $ n ++ "." ++ x)
            modNames = Map.mapWithKey (\x m -> m {FT.methodName = x})
            modArgs = Map.map (\m -> m {FT.methodArgs = ArgT Nothing (Cl Nothing (Ident n)) (Ident "self") : FT.methodArgs m})

demilkClasses :: FT.Env -> ClMap
demilkClasses env = cls'
  where
    cls = Map.mapKeys (\(Ident x) -> x) $ FT.envClasses env
    cls' = Map.map gatherFields cls
    convT :: Type -> EspressoType
    convT t = case t of
      Int _ -> EI32
      Bool _ -> EI1
      Void _ -> EVoid
      Str _ -> EStr
      Arr _ _ -> error "Arrays not implemented"
      Cl _ (Ident x) -> EClass x
    gatherFields :: FT.Class -> Class
    gatherFields c = Class {fields = Map.union myF pF, ordering = pOrd ++ myOrd, parent = p, methods = m}
      where
        m = sort $ _deident <$> Map.keys (FT.classMethods c)
        myF = Map.map convT $ Map.mapKeys (\(Ident x) -> x) $ FT.classFields c
        myOrd = sort $ map (\(Ident x) -> x) $ Map.keys $ FT.classFields c
        (Class pF pOrd _ _, p) = case FT.classBase c of
          Nothing -> (Class Map.empty [] Nothing [], Nothing)
          Just cp -> (gatherFields cp, Just $ _deident $ FT.className cp)

demilkFunctions :: ClMap -> FT.Env -> Map.Map Label Method
demilkFunctions cls env = (Map.map (demilkFunction cls env) . Map.mapKeys (\(Ident x) -> x) . FT.envFunctions) env

demilkFunction :: ClMap -> FT.Env -> FT.Method -> Method
demilkFunction cls env m =
  Method
    { args = args,
      body = LAB "Entry" : concat (reverse bodyEls'),
      types = types,
      retType = retType
    }
  where
    userArgs = map (\(ArgT _ _ i) -> i) $ FT.methodArgs m
    args = map (\(Ident x) -> if x /= "self" then "f_" ++ x else x) userArgs
    funRetTypes = Map.fromList $ (\(Ident k, v) -> (k, demilkType $ FT.methodRetType v)) <$> Map.toList (FT.envFunctions env)
    retType = demilkType $ FT.methodRetType m
    iniTypes = Map.fromList $ args `zip` ((\(ArgT _ t _) -> demilkType t) <$> FT.methodArgs m)
    cl = case break (== '.') $ _deident $ FT.methodName m of (_, "") -> Nothing; (x, _) -> Just x
    (bodyEls, types) = evalState (demilkBlock cls iniTypes (FT.methodBody m)) (Map.fromList $ zip userArgs args, 0, funRetTypes, cl)
    bodyEls' = if case retType of EVoid -> True; _ -> False then [VRET] : bodyEls else bodyEls

demilkBlock :: ClMap -> ETypeMap -> Block -> EspM ([EspressoBlock], ETypeMap)
demilkBlock cls it (BlockT _ stmts) = foldM (demilkStmt cls) ([], it) stmts

demilkStmt :: ClMap -> ([EspressoBlock], ETypeMap) -> Stmt -> EspM ([EspressoBlock], ETypeMap)
demilkStmt cls (blocks, types) stmt = case stmt of
  Empty _ -> return (blocks, types)
  BStmt ma bl -> do
    lm <- getLabMap
    (bl', tys) <- demilkBlock cls types bl
    putLabMap lm
    return (bl' ++ blocks, tys)
  Decl _ ty its -> foldM (demilkDeclaration cls $ demilkType ty) (blocks, types) its
  Ass _ ex ex' -> do 
    (bl, l, ts1) <- demilkExpr cls types ex
    let (rv, (bbl, et, field)) = if null bl then (False, _undef3) else
          case last bl of { GET v et v'  -> (True, (init bl, et, v')); _ -> (False, _undef3) }
    (bl', l', ts2) <- demilkExpr cls ts1 ex'
    if rv 
      then 
        if shouldCast (ts2 Map.! l) (ts2 Map.! l')
          then do
            let EClass cl = ts2 Map.! l
            tmp <- freshTmp
            return ([[CAST tmp cl (L l'), SET et field (L tmp)], bl', bbl] ++ blocks, Map.insert tmp (EClass cl) ts2)
          else
            return ([[SET et field (L l')], bl', bbl] ++ blocks, ts2) 
      else 
        if shouldCast (ts2 Map.! l) (ts2 Map.! l')
          then do
            let EClass cl = ts2 Map.! l
            tmp <- freshTmp
            return ([[CAST tmp cl (L l'), CPY l (L tmp)], bl', bl] ++ blocks, Map.insert tmp (EClass cl) ts2)
          else
            return ([[CPY l (L l')], bl', bl] ++ blocks, ts2)
  Incr ma id -> undefined -- Should have been desugared
  Decr ma id -> undefined -- Should have been desugared
  Ret _ ex -> demilkExpr cls types ex >>= \(bl, l, ts) -> return ([[RET (L l)], bl] ++ blocks, ts)
  VRet _ -> return ([VRET] : blocks, types)
  Cond _ ex st -> do
    (ebl, el, ts1) <- demilkExpr cls types ex
    (sbl, ts2) <- demilkStmt cls ([], ts1) st
    jmp <- freshLabel
    let lend = "Lendif_" ++ jmp
    let ltrue = "Ltrue_" ++ jmp
    let cond = [[BR lend, LAB lend]] ++ sbl ++ [[CBR (L el) ltrue lend, LAB ltrue], ebl]
    return (cond ++ blocks, ts2)
  CondElse _ ex st st' -> do
    (ebl, el, ts1) <- demilkExpr cls types ex
    (sbl, ts2) <- demilkStmt cls ([], ts1) st
    (sbl', ts3) <- demilkStmt cls ([], ts2) st'
    jmp <- freshLabel
    let lend = "Lendif_" ++ jmp
    let lfalse = "Lfalse_" ++ jmp
    let ltrue = "Ltrue_" ++ jmp
    let cond = [[CBR (L el) ltrue lfalse], ebl]
    let tblock = [[BR lend]] ++ sbl ++ [[LAB ltrue]]
    let fblock = [[BR lend, LAB lend]] ++ sbl' ++ [[LAB lfalse]]
    return (fblock ++ tblock ++ cond ++ blocks, ts3)
  While _ ex st -> do
    (ebl, el, ts1) <- demilkExpr cls types ex
    (body, ts2) <- demilkStmt cls ([], ts1) st
    jmp <- freshLabel
    let lwhile = "Lwhile_" ++ jmp
    let lbody = "Lbody_" ++ jmp
    let lend = "Lendwhile_" ++ jmp
    let cond = [[CBR (L el) lbody lend], ebl, [BR lwhile, LAB lwhile]]
    let bodyBlock = [[BR lwhile, LAB lend]] ++ body ++ [[LAB lbody]]
    return (bodyBlock ++ cond ++ blocks, ts2)
  For ma ty id ex st -> undefined -- Should have been desugared
  SExp _ ex -> demilkExpr cls types ex >>= \(bl, _, ts) -> return (bl : blocks, ts)

demilkDeclaration :: ClMap -> EspressoType -> ([EspressoBlock], ETypeMap) -> Item -> EspM ([EspressoBlock], ETypeMap)
demilkDeclaration cls ty (blocks, types) (Init _ n ex) = do
  (ebl, el, ts1) <- demilkExpr cls types ex
  lab <- freshLabel
  let ul = userLabel lab n
  getLabMap >>= putLabMap . Map.insert n ul
  if shouldCast ty (ts1 Map.! el) then do
    let EClass cl = ty
    return ([[CAST ul cl (L el)], ebl] ++ blocks, Map.insert ul ty ts1)
  else
    return ([[CPY ul (L el)], ebl] ++ blocks, Map.insert ul ty ts1)
demilkDeclaration cls ty (blocks, types) (NoInit _ n) = do
  lab <- freshLabel
  let ul = userLabel lab n
  let val = defaultValue cls ty
  getLabMap >>= putLabMap . Map.insert n ul
  return ([CPY ul val] : blocks, Map.insert ul ty types)

shouldCast :: EspressoType -> EspressoType -> Bool
shouldCast (EClass x) (EClass y) = x /= y
shouldCast _ _ = False

demilkExpr :: ClMap -> ETypeMap -> Expr -> EspM (EspressoBlock, Label, ETypeMap)
demilkExpr cls types (EVar _ id) = do
  m <- getLabMap
  case m Map.!? id of
    Just l -> return ([], l, types)
    Nothing -> do
      tmp <- freshTmp
      cl <- getClass
      when (isNothing cl) $ error $ "Variable " ++ show id ++ " not found"
      let Ident field = id
      let fieldTy = fromJust $ Map.lookup field $ fields $ fromJust $ Map.lookup (fromJust cl) cls
      return ([GET tmp (L "self") field], tmp, Map.insert tmp fieldTy types)
demilkExpr cls types (ELitInt _ n) = do
  tmp <- freshTmp
  return ([CPY tmp (V $ VInt n)], tmp, Map.insert tmp EI32 types)
demilkExpr cls types (EString _ s) = do
  tmp <- freshTmp
  return ([CPY tmp (V $ VString s)], tmp, Map.insert tmp EStr types)
demilkExpr cls types (ELitTrue _) = do
  tmp <- freshTmp
  return ([CPY tmp (V espTrue)], tmp, Map.insert tmp EI1 types)
demilkExpr cls types (ELitFalse _) = do
  tmp <- freshTmp
  return ([CPY tmp (V espFalse)], tmp, Map.insert tmp EI1 types)
demilkExpr cls types (EFun _ (Ident id) exs) = do
  (bls, args, tslst) <- unzip3 <$> mapM (demilkExpr cls types) exs
  let ts = foldl Map.union types tslst
  cl <- getClass
  
  let (nm, isM) = case cl of 
        Just c -> case methodOwner cls id c of
          Just o -> (o ++ "." ++ id, True)
          Nothing -> (id, False)
        Nothing -> (id, False)
  fr <- getFunRetType nm
  let blocks = concat $ reverse bls
  tmp <- freshTmp
  let args' = if isM then L "self":(L <$> args) else  L <$> args
  return (blocks ++ [CALL tmp nm args'], tmp, Map.insert tmp fr ts)
demilkExpr cls types (ENeg _ ex) = do
  (bl, l, ts) <- demilkExpr cls types ex
  tmp <- freshTmp
  return (bl ++ [NEG tmp (L l)], tmp, Map.insert tmp EI32 ts)
demilkExpr cls types (ENot _ ex) = do
  (bl, l, ts) <- demilkExpr cls types ex
  tmp <- freshTmp
  return (bl ++ [NOT tmp (L l)], tmp, Map.insert tmp EI1 ts)
demilkExpr cls types (EMul _ ex mo ex') = do
  (bl, l, ts1) <- demilkExpr cls types ex
  (bl', l', ts2) <- demilkExpr cls ts1 ex'
  tmp <- freshTmp
  let op = case mo of
        Times _ -> MUL
        Div _ -> DIV
        Mod _ -> MOD
  return (bl ++ bl' ++ [op tmp (L l) (L l')], tmp, Map.insert tmp EI32 ts2)
demilkExpr cls types (EAdd _ ex ao ex') = do
  (bl, l, ts1) <- demilkExpr cls types ex
  (bl', l', ts2) <- demilkExpr cls ts1 ex'
  tmp <- freshTmp
  let op = case ao of
        Plus _ -> ADD
        Minus _ -> SUB
  return (bl ++ bl' ++ [op tmp (L l) (L l')], tmp, Map.insert tmp (ts2 `lookupik` l) ts2)
demilkExpr cls types (ERel _ ex ro ex') = do
  (bl, l, ts1) <- demilkExpr cls types ex
  (bl', l', ts2) <- demilkExpr cls ts1 ex'
  tmp <- freshTmp
  let op = case ro of
        LTH _ -> LRT
        LE _ -> LRE
        GTH _ -> GRT
        GE _ -> GRE
        EQU _ -> EQS
        NE _ -> NEQ
  return (bl ++ bl' ++ [op tmp (L l) (L l')], tmp, Map.insert tmp EI1 ts2)
demilkExpr cls types (EAnd _ ex ex') = do
  (bl, l, ts1) <- demilkExpr cls types ex
  (bl', l', ts2) <- demilkExpr cls ts1 ex'
  tmp <- freshTmp
  lab <- freshLabel
  let lcont = "Lcontand_" ++ lab
  let lstop = "Lstopand_" ++ lab
  let lend = "Lendand_" ++ lab
  let v = [CPY tmp (L l'), BR lend, LAB lstop, CPY tmp (V espFalse), BR lend, LAB lend]
  return (bl ++ [CBR (L l) lcont lstop, LAB lcont] ++ bl' ++ v, tmp, Map.insert tmp EI1 ts2)
demilkExpr cls types (EOr _ ex ex') = do
  (bl, l, ts1) <- demilkExpr cls types ex
  (bl', l', ts2) <- demilkExpr cls ts1 ex'
  tmp <- freshTmp
  lab <- freshLabel
  let lcont = "Lcontor_" ++ lab
  let lstop = "Lstopor_" ++ lab
  let lend = "Lendor_" ++ lab
  let v = [CPY tmp (L l'), BR lend, LAB lstop, CPY tmp (V espTrue), BR lend, LAB lend]
  return (bl ++ [CBR (L l) lstop lcont, LAB lcont] ++ bl' ++ v, tmp, Map.insert tmp EI1 ts2)

demilkExpr cls types (ECast _ ty) = case ty of
  Cl _ (Ident x) -> do
    tmp <- freshTmp
    return ([CPY tmp (V (VNull x))], tmp, Map.insert tmp (EClass x) types)
  _ -> error "Error: Arrays not implemented"
demilkExpr cls types (EAcc _ ex (Ident field)) = do
  (bl, l, ts) <- demilkExpr cls types ex
  let (EClass x) = ts `lookupik` l
  let t = fields (cls `lookupik` x) `lookupik` field
  tmp <- freshTmp
  return (bl ++ [GET tmp (L l) field], tmp, Map.insert tmp t ts)
demilkExpr cls types (ENew _ ty) = do
  t <- freshTmp
  let (EClass x) = demilkType ty
  return ([NEW t x], t, Map.insert t (EClass x) types)

demilkExpr cls types (EMth _ ex (Ident id) exs) = do
  (bl, l, ts1) <- demilkExpr cls types ex
  (bls, args, tslst) <- unzip3 <$> mapM (demilkExpr cls types) exs
  let ts2 = foldl Map.union ts1 tslst
  let EClass cln = ts2 `lookupik` l
  let owner = fromMaybe (error $ "Error: Method " ++ id ++ " not found in class " ++ cln) $ methodOwner cls id cln
  let mname = owner ++ "." ++ id
  fr <- getFunRetType mname
  let blocks = concat $ reverse bls
  tmp <- freshTmp
  if owner == cln
    then return (bl ++ blocks ++ [CALL tmp mname (L l : (L <$> args))], tmp, Map.insert tmp fr ts2)
    else do
      tmp2 <- freshTmp
      let ts3 = Map.insert tmp (EClass owner) ts2
      return (bl ++ blocks ++ [CAST tmp owner (L l), CALL tmp2 mname (L tmp : (L <$> args))], tmp, Map.insert tmp2 fr ts3)

demilkExpr cls _ (EInd ma ex ex') = error "Error: Arrays not implemented" -- Next iteration.
demilkExpr cls _ (ENewArr ma ty ex) = error "Error: Arrays not implemented" -- Next iteration.
demilkExpr cls _ (ECastId ma ex) = undefined -- Should have been desugared.
demilkExpr cls _ (ECastArr ma ty) = undefined -- Should have been desugared.

methodOwner :: ClMap -> String -> String -> Maybe String
methodOwner cls mname cln = case find (== mname) (methods (cls `lookupik` cln)) of
  Just _ -> Just cln
  Nothing -> case parent (cls `lookupik` cln) of
    Just x -> methodOwner cls mname x
    Nothing -> Nothing

demilkType :: Type -> EspressoType
demilkType (Int _) = EI32
demilkType (Str _) = EStr
demilkType (Bool _) = EI1
demilkType (Void _) = EVoid
demilkType (Cl _ (Ident x)) = EClass x
demilkType _ = undefined

getVal :: Map.Map Label Value -> ET -> IO Value
getVal env (L s) = return $ env `lookupik` s
getVal env (V v) = return v

defaultValue :: ClMap -> EspressoType -> ET
defaultValue cls EI32 = V $ VInt 0
defaultValue cls EStr = V $ VString ""
defaultValue cls EI1 = V $ VBool False
defaultValue cls EVoid = undefined
defaultValue cls (EClass x) = V $ VNull x

_undef3 :: (a, b, c)
_undef3 = (undefined, undefined, undefined)

_deident :: Ident -> String
_deident (Ident x) = x