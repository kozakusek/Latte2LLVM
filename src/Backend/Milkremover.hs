{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}
module Backend.Milkremover where

import Control.Monad.Identity (Identity)
import Control.Monad.State (State, StateT, evalState, foldM, forM, get, put, replicateM)
import qualified Data.Map as Map
import qualified Frontend.Typechecker as FT
import Latte.Abs
import Data.List (foldl', elemIndex)
import Control.Monad (foldM_, void, mapAndUnzipM)
import Data.Map (member)
import Data.Maybe (fromJust, fromMaybe)

lookupik m k = case Map.lookup k m of
  Just v -> v
  Nothing -> error $ "lookupik: " ++ show k ++ " not found in " ++ show m

type Label = String

data Value = VInt Integer | VBool Bool | VString String deriving (Eq, Ord)

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
  | LAB Label deriving (Eq, Ord)
-- Array Access
-- Field Acces
-- Memory Dereference
-- ...

type EspressoBlock = [Instruction]
data EspressoType = EI1 | EI32 | EStr | EVoid
type ETypeMap = Map.Map Label EspressoType

data Method = Method
  { args :: [Label],
    body :: EspressoBlock,
    types :: ETypeMap,
    retType :: EspressoType
  }

data Espresso = Espresso
  { functions :: Map.Map Label Method
  -- classes :: Map.Map Label Class
  }

instance Show Value where
  show (VInt i) = show i
  show (VString s) = show s
  show (VBool b) = show b

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

instance Show Method where
  show (Method args body _ t) = show t ++ " fn(args = " ++ show args ++ ") {\n" ++ unlines (("\t" ++) . show <$> body) ++ "}\n"

instance Show Espresso where
  show (Espresso functions) = unlines $ map (\(n, f) -> n ++ " = " ++ show f) $ Map.toList functions

instance Show EspressoType where
  show EI1 = "i1"
  show EI32 = "i32"
  show EStr = "str"
  show EVoid = "void"

type LabMap = Map.Map Ident Label

type EspM = State (LabMap, Integer, Map.Map String EspressoType)

freshLabel :: EspM Label
freshLabel = do
  (m, i, fr) <- get
  put (m, i + 1, fr)
  return $ show i

freshTmp :: EspM Label
freshTmp = do
  (m, i, fr) <- get
  put (m, i + 1, fr)
  return $ "e_" ++ show i

getLabMap :: EspM LabMap
getLabMap = do
  (m, i, fr) <- get
  return m

putLabMap :: LabMap -> EspM ()
putLabMap m = do
  (m', i, fr) <- get
  put (m, i, fr)

getFunRetType :: String -> EspM EspressoType
getFunRetType f = do
  (m, i, fr) <- get
  case fr Map.!? f of
    Just t -> return t
    Nothing -> return $ demilkType $ FT.methodRetType $ FT.builtinMethods `lookupik`   Ident f

userLabel :: Label -> Ident -> Label
userLabel id (Ident x) = "u_" ++ id ++ "_" ++ x

removeMilk :: FT.Env -> Espresso
removeMilk env = Espresso {functions = demilkFunctions env}

demilkFunctions :: FT.Env -> Map.Map Label Method
demilkFunctions env = (Map.map (demilkFunction env) . Map.mapKeys (\(Ident x) -> x) . FT.envFunctions) env

demilkFunction :: FT.Env -> FT.Method -> Method
demilkFunction env m = Method {
    args = args,
    body = LAB "Entry":concat (reverse bodyEls'),
    types = types,
    retType = retType
  }
  where
    userArgs = map (\(ArgT _ _ i) -> i) $ FT.methodArgs m
    args = map (\(Ident x) -> "f_" ++ x) userArgs
    funRetTypes = Map.fromList $ (\(Ident k, v) -> (k, demilkType $ FT.methodRetType v)) <$> Map.toList (FT.envFunctions env)
    retType = demilkType $ FT.methodRetType m
    iniTypes = Map.fromList $ args `zip` ((\(ArgT _ t _) -> demilkType t) <$> FT.methodArgs m)
    (bodyEls, types) = evalState (demilkBlock iniTypes (FT.methodBody m)) (Map.fromList $ zip userArgs args, 0, funRetTypes)
    bodyEls' = if case retType of { EVoid -> True; _ -> False} then [VRET]:bodyEls else bodyEls


demilkBlock :: ETypeMap -> Block -> EspM ([EspressoBlock], ETypeMap)
demilkBlock it (BlockT _ stmts) = foldM demilkStmt ([], it) stmts

demilkStmt :: ([EspressoBlock], ETypeMap) -> Stmt -> EspM ([EspressoBlock], ETypeMap)
demilkStmt (blocks, types) stmt = case stmt of
  Empty _ -> return (blocks, types)
  BStmt ma bl -> do
    lm <- getLabMap
    (bl', tys) <- demilkBlock types bl
    putLabMap lm
    return (bl' ++ blocks, tys)
  Decl _ ty its -> foldM (demilkDeclaration $ demilkType ty) (blocks, types) its
  Ass _ ex ex' -> do
    (bl, l, ts1) <- demilkExpr types ex
    (bl', l', ts2) <- demilkExpr ts1 ex'
    return ([[CPY l (L l')], bl', bl] ++ blocks, ts2)
  Incr ma id -> undefined -- Should have been desugared
  Decr ma id -> undefined -- Should have been desugared
  Ret _ ex -> demilkExpr types ex >>= \(bl, l, ts) -> return ([[RET (L l)], bl] ++ blocks, ts)
  VRet _ -> return ([VRET] : blocks, types)
  Cond _ ex st -> do
    (ebl, el, ts1) <- demilkExpr types ex
    (sbl, ts2) <- demilkStmt ([], ts1) st
    jmp <- freshLabel
    let lend = "Lendif_" ++ jmp
    let ltrue = "Ltrue_" ++ jmp
    let cond = [[BR lend, LAB lend]] ++ sbl ++ [[CBR (L el) ltrue lend, LAB ltrue], ebl]
    return (cond ++ blocks, ts2)
  CondElse _ ex st st' -> do
    (ebl, el, ts1) <- demilkExpr types ex
    (sbl, ts2) <- demilkStmt ([], ts1) st
    (sbl', ts3) <- demilkStmt ([], ts2) st'
    jmp <- freshLabel
    let lend = "Lendif_" ++ jmp
    let lfalse = "Lfalse_" ++ jmp
    let ltrue = "Ltrue_" ++ jmp
    let cond = [[CBR (L el) ltrue lfalse], ebl]
    let tblock = [[BR lend]] ++ sbl ++ [[LAB ltrue]]
    let fblock = [[BR lend, LAB lend]] ++ sbl' ++ [[LAB lfalse]]
    return (fblock ++ tblock ++ cond ++ blocks, ts3)
  While _ ex st -> do
    (ebl, el, ts1) <- demilkExpr types ex
    (body, ts2) <- demilkStmt ([], ts1) st
    jmp <- freshLabel
    let lwhile = "Lwhile_" ++ jmp
    let lbody = "Lbody_" ++ jmp
    let lend = "Lendwhile_" ++ jmp
    let cond = [[CBR (L el) lbody lend], ebl, [BR lwhile, LAB lwhile]]
    let bodyBlock = [[BR lwhile, LAB lend]] ++ body ++ [[LAB lbody]]
    return (bodyBlock ++ cond ++ blocks, ts2)
  For ma ty id ex st -> undefined -- Should have been desugared
  SExp _ ex -> demilkExpr types ex >>= \(bl, _, ts) -> return (bl : blocks, ts)

demilkDeclaration :: EspressoType -> ([EspressoBlock], ETypeMap) -> Item -> EspM ([EspressoBlock], ETypeMap)
demilkDeclaration ty (blocks, types) (Init _ n ex) = do
  (ebl, el, ts1) <- demilkExpr types ex
  lab <- freshLabel
  let ul = userLabel lab n
  getLabMap >>= putLabMap . Map.insert n ul
  return ([[CPY ul (L el)], ebl] ++ blocks, Map.insert ul ty ts1)
demilkDeclaration ty (blocks, types) (NoInit _ n) = do
  lab <- freshLabel
  let ul = userLabel lab n
  let val = case ty of
        EStr -> V $ VString ""
        _ -> V $ VInt 0
  getLabMap >>= putLabMap . Map.insert n ul
  return ([CPY ul val] : blocks, Map.insert ul ty types)

demilkExpr :: ETypeMap -> Expr -> EspM (EspressoBlock, Label, ETypeMap)
demilkExpr types (EVar _ id) = do
  m <- getLabMap
  return ([], m `lookupik` id, types)
demilkExpr types (ELitInt _ n) = do
  tmp <- freshTmp
  return ([CPY tmp (V $ VInt n)], tmp, Map.insert tmp EI32 types)
demilkExpr types (EString _ s) = do
  tmp <- freshTmp
  return ([CPY tmp (V $ VString s)], tmp, Map.insert tmp EStr types)
demilkExpr types (ELitTrue _) = do
  tmp <- freshTmp
  return ([CPY tmp (V espTrue)], tmp, Map.insert tmp EI1 types)
demilkExpr types (ELitFalse _) = do
  tmp <- freshTmp
  return ([CPY tmp (V espFalse)], tmp, Map.insert tmp EI1 types)
demilkExpr types (EFun _ (Ident id) exs) = do
  (bls, args, tslst) <- unzip3 <$> mapM (demilkExpr types) exs
  let ts = foldl Map.union types tslst
  fr <- getFunRetType id
  let blocks = concat $ reverse bls
  tmp <- freshTmp
  return (blocks ++ [CALL tmp id (L <$> args)], tmp, Map.insert tmp fr ts)
demilkExpr types (ENeg _ ex) = do
  (bl, l, ts) <- demilkExpr types ex
  tmp <- freshTmp
  return (bl ++ [NEG tmp (L l)], tmp, Map.insert tmp EI32 ts)
demilkExpr types (ENot _ ex) = do
  (bl, l, ts) <- demilkExpr types ex
  tmp <- freshTmp
  return (bl ++ [NOT tmp (L l)], tmp, Map.insert tmp EI1 ts)
demilkExpr types (EMul _ ex mo ex') = do
  (bl, l, ts1) <- demilkExpr types ex
  (bl', l', ts2) <- demilkExpr ts1 ex'
  tmp <- freshTmp
  let op = case mo of
        Times _ -> MUL
        Div _ -> DIV
        Mod _ -> MOD
  return (bl ++ bl' ++ [op tmp (L l) (L l')], tmp, Map.insert tmp EI32 ts2)
demilkExpr types (EAdd _ ex ao ex') = do
  (bl, l, ts1) <- demilkExpr types ex
  (bl', l', ts2) <- demilkExpr ts1 ex'
  tmp <- freshTmp
  let op = case ao of
        Plus _ -> ADD
        Minus _ -> SUB
  return (bl ++ bl' ++ [op tmp (L l) (L l')], tmp, Map.insert tmp (ts2 `lookupik`   l) ts2)
demilkExpr types (ERel _ ex ro ex') = do
  (bl, l, ts1) <- demilkExpr types ex
  (bl', l', ts2) <- demilkExpr ts1 ex'
  tmp <- freshTmp
  let op = case ro of
        LTH _ -> LRT
        LE _ -> LRE
        GTH _ -> GRT
        GE _ -> GRE
        EQU _ -> EQS
        NE _ -> NEQ
  return (bl ++ bl' ++ [op tmp (L l) (L l')], tmp, Map.insert tmp EI1 ts2)
demilkExpr types (EAnd _ ex ex') = do
    (bl, l, ts1) <- demilkExpr types ex
    (bl', l', ts2) <- demilkExpr ts1 ex'
    tmp <- freshTmp
    lab <- freshLabel
    let lcont = "Lcontand_" ++ lab
    let lstop = "Lstopand_" ++ lab
    let lend = "Lendand_" ++ lab
    let v = [CPY tmp (L l'), BR lend, LAB lstop, CPY tmp (V espFalse), BR lend, LAB lend]
    return (bl ++ [CBR (L l) lcont lstop, LAB lcont] ++ bl' ++ v, tmp, Map.insert tmp EI1 ts2)
demilkExpr types (EOr _ ex ex') = do
    (bl, l, ts1) <- demilkExpr types ex
    (bl', l', ts2) <- demilkExpr ts1 ex'
    tmp <- freshTmp
    lab <- freshLabel
    let lcont = "Lcontor_" ++ lab
    let lstop = "Lstopor_" ++ lab
    let lend = "Lendor_" ++ lab
    let v = [CPY tmp (L l'), BR lend, LAB lstop, CPY tmp (V espTrue), BR lend, LAB lend]
    return (bl ++ [CBR (L l) lstop lcont, LAB lcont] ++ bl' ++ v, tmp, Map.insert tmp EI1 ts2)
demilkExpr _ (ECast ma ty) = error "Error: Casting not implemented" -- Next iteration.
demilkExpr _ (EMth ma ex id exs) = error "Error: Classes not implemented" -- Next iteration.
demilkExpr _ (EInd ma ex ex') = error "Error: Arrays and classes not implemented" -- Next iteration.
demilkExpr _ (EAcc ma ex id) = error "Error: Arrays not implemented" -- Next iteration.
demilkExpr _ (ENew ma ty) = error "Error: Classes not implemented" -- Next iteration.
demilkExpr _ (ENewArr ma ty ex) = error "Error: Arrays not implemented" -- Next iteration.
demilkExpr _ (ECastId ma ex) = undefined -- Should have been desugared.
demilkExpr _ (ECastArr ma ty) = undefined -- Should have been desugared.

demilkType :: Type -> EspressoType
demilkType (Int _) = EI32
demilkType (Str _) = EStr
demilkType (Bool _) = EI1
demilkType (Void _) = EVoid
demilkType _ = undefined

getVal :: Map.Map Label Value -> ET -> IO Value
getVal env (L s) = return $ env `lookupik`   s
getVal env (V v) = return v

