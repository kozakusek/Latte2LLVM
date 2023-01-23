{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Frontend.Typechecker where

import Control.Monad (foldM, forM_, unless, void, when)
import Control.Monad.State (MonadState (get, put), execStateT)
import Control.Monad.State.Lazy (StateT)
import Data.Either (fromLeft, fromRight, isRight)
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe, isNothing)
import Data.Set (Set)
import qualified Data.Set as Set
import Latte.Abs (AddOp, AddOp' (..), Arg, Arg' (..), BNFC'Position, Block, Block' (BlockT), ClBlock, ClBlock' (ClBlockT), Expr, Expr' (..), Ident (..), InClDef, InClDef' (..), Item' (..), MulOp, MulOp' (..), Program, Program' (ProgramT), RelOp, RelOp' (..), Stmt, Stmt' (..), TopDef, TopDef' (..), Type, Type' (..))
import Latte.Skel (Err)

data Class = Class
  { className :: Ident,
    classBase :: Maybe Class,
    _baseCanditate :: Maybe Ident,
    classFields :: Map.Map Ident Type,
    classMethods :: Map.Map Ident Method
  }
  deriving (Show, Eq)

data Method = Method
  { methodName :: Ident,
    methodRetType :: Type,
    methodThis :: Either Ident Class,
    methodArgs :: [Arg],
    methodBody :: Block
  }
  deriving (Show, Eq)

data Env = Env
  { envClasses :: Map.Map Ident Class,
    envFunctions :: Map.Map Ident Method,
    envVariables :: Map.Map Ident Type,
    envInnerVariables :: Map.Map Ident Type
  }
  deriving (Show, Eq)

type EnvM a = StateT Env Err a

instance MonadFail Err where
  fail = Left

typeCheck :: Program -> Err Env
typeCheck p = do
  env <- classes p -- Gather classes with their attributes and methods
  env <- resolveCandiates env -- And check for cycles in class hierarchy
  checkVirtuals env -- Verify virtual methods types
  env <- functions p env -- Gather functions
  checkMain env --    Check if main is defined and has proper signature
  verifyTypes env -- Verify all types with function argument collisions,
  --    use of undeclared variables, repeated declarations, etc.)
  let env' = removeDeadCode env -- Remove trivially dead code
  checkReturns env' -- Check if all non-void paths return a value
  return $ removeBulitinMethods env'

classes :: Program -> Err Env
classes (ProgramT _ defs) =
  foldM addClass (Env Map.empty Map.empty Map.empty Map.empty) defs

addClass :: Env -> TopDef -> Err Env
addClass env (ClDef _ name block) = do
  when (Set.member name forbiddenTypes) $
    fail $
      "Class name " ++ show name ++ " is reserved"
  when (Map.member name $ envClasses env) $
    fail $
      "Class " ++ show name ++ " already defined"
  cl <- createClass name Nothing block
  return env {envClasses = Map.insert name cl (envClasses env)}
addClass env (SubClDef _ name base block) = do
  when (Set.member name forbiddenTypes) $
    fail $
      "Class name " ++ show name ++ " is reserved"
  when (Map.member name $ envClasses env) $
    fail $
      "Class " ++ show name ++ " already defined"
  cl <- createClass name (Just base) block
  return env {envClasses = Map.insert name cl (envClasses env)}
addClass env _ = return env

createClass :: Ident -> Maybe Ident -> ClBlock -> Err Class
createClass name base (ClBlockT _ defs) = do
  fields <- foldM (addClField name) Map.empty defs
  methods <- foldM (addClMethod name fields) Map.empty defs
  return $ Class name Nothing base fields methods

addClMethod :: Ident -> Map.Map Ident Type -> Map.Map Ident Method -> InClDef -> Err (Map.Map Ident Method)
addClMethod cl fields methods (MthDef p ty name ars block) = do
  let method = Method name ty (Left cl) ars block
  when (Map.member name fields) $ fail $ "Error" ++ showPos p ++ ": Class " ++ ident cl ++ " already contains field " ++ ident name
  when (Map.member name methods) $ fail $ "Error" ++ showPos p ++ ": Method " ++ ident name ++ " has duplicate definitions in class " ++ ident cl
  when (argRepetion ars) $ fail $ "Error" ++ showPos p ++ ": Method " ++ ident name ++ " has two arguments with the same name in class " ++ ident cl
  when (isArrArr ty) $ fail $ "Error" ++ showPos p ++ ": Method " ++ ident name ++ " has array of arrays return type in class " ++ ident cl
  return $ Map.insert name method methods
addClMethod cl _ methods _ = return methods

argRepetion :: [Arg] -> Bool
argRepetion args = length args /= length (Set.fromList (map (\(ArgT _ _ name) -> name) args))

addClField :: Ident -> Map.Map Ident Type -> InClDef -> Err (Map.Map Ident Type)
addClField cl fields (FldDef p t name) = do
  when (isArrArr t) $ fail $ "Error" ++ showPos p ++ ": Field " ++ ident name ++ " has array of arrays type in class " ++ ident cl
  if Map.member name fields
    then fail $ "Error" ++ showPos p ++ ": Class " ++ ident cl ++ " already contains field " ++ ident name
    else return $ Map.insert name t fields
addClField cl fields _ = return fields

resolveCandiates :: Env -> Err Env
resolveCandiates env = do
  let classes = envClasses env
  resolvedClasses <- auxCl classes Nothing Map.empty
  let resolvedClassesWithMethods = Map.map (\cl -> cl {classMethods = auxM resolvedClasses (classMethods cl)}) resolvedClasses
  return env {envClasses = resolvedClassesWithMethods}
  where
    auxCl :: Map.Map Ident Class -> Maybe Class -> Map.Map Ident Class -> Err (Map.Map Ident Class)
    auxCl classes Nothing resolved = if Map.null classes then return resolved else auxCl (Map.deleteAt 0 classes) (Just $ snd $ Map.elemAt 0 classes) resolved
    auxCl classes (Just cl) resolved
      | Map.member (className cl) resolved = auxCl classes Nothing resolved
      | isNothing $ _baseCanditate cl = auxCl classes Nothing (Map.insert (className cl) cl resolved)
      | otherwise = do
          let cand = fromJust $ _baseCanditate cl
          if Map.member cand resolved
            then auxCl classes Nothing (Map.insert (className cl) (cl {classBase = Just $ resolved Map.! cand}) resolved)
            else
              if Map.member cand classes
                then do
                  res <- auxCl (Map.delete cand classes) (Just $ classes Map.! cand) resolved
                  auxCl classes (Just $ cl {classBase = Just $ res Map.! cand}) res
                else fail $ "Error: Could not resolve class hierarchy for class " ++ ident (className cl)
    auxM :: Map.Map Ident Class -> Map.Map Ident Method -> Map.Map Ident Method
    auxM classes = Map.map (\m -> m {methodThis = Right $ classes Map.! fromLeft undefined (methodThis m)})

checkVirtuals :: Env -> Err ()
checkVirtuals env = forM_ (map snd $ Map.assocs $ envClasses env) (checkVirtualsCl Map.empty Set.empty)

checkVirtualsCl :: Map.Map Ident Method -> Set.Set Ident -> Class -> Err ()
checkVirtualsCl methods fields cl = do
  let pM = classMethods cl
  forM_ (Map.assocs pM) $ \(name, m) -> do
    when (Map.member name methods) $ do
      let m' = methods Map.! name
      unless (isSameType (methodRetType m) (methodRetType m')) $ fail $ "Error: Method " ++ ident name ++ " has different return type in class " ++ ident (className cl)
      when (length (methodArgs m) /= length (methodArgs m')) $ fail $ "Error: Method " ++ ident name ++ " has different number of arguments in class " ++ ident (className cl)
      forM_ (zip (methodArgs m) (methodArgs m')) $ \(a, a') -> do
        when (argType a /= argType a') $ fail $ "Error: Method " ++ ident name ++ " has different argument types in class " ++ ident (className cl)
  let pF = Set.fromList $ Map.keys $ classFields cl
  forM_  pF $ \name -> do
    when (Set.member name fields) $ fail $ "Error: Field " ++ ident name ++ " is already defined in class " ++ ident (className cl)
  forM_ (classBase cl) (checkVirtualsCl (Map.union pM methods) (Set.union pF fields))

functions :: Program -> Env -> Err Env
functions (ProgramT _ defs) env = foldM addFunction (env {envFunctions = builtinMethods}) defs

addFunction :: Env -> TopDef -> Err Env
addFunction env (FnDef p ty id ars bl) = do
  when (Map.member id (envFunctions env)) $ fail $ "Error" ++ showPos p ++ ": Function " ++ ident id ++ " has duplicate definitions"
  when (argRepetion ars) $ fail $ "Error" ++ showPos p ++ ": Function " ++ ident id ++ " has two arguments with the same name"
  when (isArrArr ty) $ fail $ "Error" ++ showPos p ++ ": Function " ++ ident id ++ " has array of arrays as return type"
  return $ env {envFunctions = Map.insert id (Method id ty (Left id) ars bl) (envFunctions env)}
addFunction env _ = return env

checkMain :: Env -> Err ()
checkMain env =
  if Map.member (Ident "main") (envFunctions env)
    then do
      let main = envFunctions env Map.! Ident "main"
      if isInt (methodRetType main) && null (methodArgs main)
        then return ()
        else fail "Error: main function must be of type int and take no arguments"
    else fail "Error: main function not defined"

verifyTypes :: Env -> Err ()
verifyTypes env = do
  forM_ (Map.elems $ envFunctions env) (\m -> execStateT (verifyMethod m) env)
  forM_ (concatMap (Map.elems . classMethods) (Map.elems (envClasses env))) (\m -> execStateT (verifyMethod m) env)

verifyMethod :: Method -> EnvM ()
verifyMethod m = do
  env <- get

  let self = methodThis m
  when (isRight self) $ do
    let cl = fromRight undefined self
    let env_s = env {envInnerVariables = Map.insert (Ident "self") (Cl Nothing $ className cl) (envInnerVariables env)}
    let env_sf = env_s {envVariables = Map.union (classFields cl) (envVariables env_s)}
    let env_sfm = env_sf {envFunctions = Map.union (classMethods cl) (envFunctions env_sf)}
    put env_sfm
  forM_
    (methodArgs m)
    ( \(ArgT _ t id) -> do
        tenv <- get
        put tenv {envInnerVariables = Map.insert id t (envInnerVariables tenv)}
    )

  let (BlockT _ stmts) = methodBody m
  forM_ stmts (verifyStmt m)
  put env

verifyStmt :: Method -> Stmt -> EnvM ()
verifyStmt m (Empty _) = return ()
verifyStmt m (BStmt pos (BlockT _ stmts)) = do
  env <- get
  put $ env {envVariables = Map.union (envInnerVariables env) (envVariables env), envInnerVariables = Map.empty}
  forM_ stmts (verifyStmt m)
  put env
verifyStmt m (Decl pos ty its) = do
  when (isArrArr ty) $ fail $ "Error" ++ showPos pos ++ ": Variable declaration has array of arrays as type"
  when (isVoid ty) $ fail $ "Error" ++ showPos pos ++ ": Variable declaration has void as type"
  forM_
    its
    ( \item -> do
        env <- get
        let (pos, name) = posname item
        when (Set.member name forbiddenVars) $ fail $ "Error" ++ showPos pos ++ ": Variable " ++ ident name ++ " is reserved"
        when (Map.member name (envInnerVariables env)) $ fail $ "Error" ++ showPos pos ++ ": Variable " ++ ident name ++ " has duplicate definitions"
        case item of
          Init _ _ ex -> do
            t <- verifyExpr m ex
            unless (isSubtype env ty t) $ fail $ "Error" ++ showPos pos ++ ": Type mismatch in initialization of variable " ++ ident name ++ ". Expected " ++ showType ty ++ " but got " ++ showType t
          _ -> return ()
        put $ env {envInnerVariables = Map.insert name ty (envInnerVariables env)}
    )
  where
    posname (NoInit pos name) = (pos, name)
    posname (Init pos name _) = (pos, name)
verifyStmt m (Ass pos ex ex') = do
  t <- verifyExpr m ex
  t' <- verifyExpr m ex'
  env <- get
  unless (isSubtype env t t') $ fail $ "Error" ++ showPos pos ++ ": Type mismatch in assignment. Expected " ++ showType t ++ " but got " ++ showType t'
verifyStmt m (Incr pos id) = undefined -- Should have been desugared
verifyStmt m (Decr pos id) = undefined -- Should have been desugared
verifyStmt m (Ret pos ex) = do
  let ty = methodRetType m
  if isVoid ty
    then fail $ "Error" ++ showPos pos ++ ": Method " ++ ident (methodName m) ++ " is void and cannot return a value"
    else do
      exTy <- verifyExpr m ex
      env <- get
      if isSubtype env ty exTy
        then return ()
        else fail $ "Error" ++ showPos pos ++ ": Method " ++ ident (methodName m) ++ " should return " ++ showType ty ++ " but returns " ++ showType exTy
verifyStmt m (VRet pos) =
  if isVoid (methodRetType m)
    then return ()
    else fail $ "Error" ++ showPos pos ++ ": Non-void function " ++ ident (methodName m) ++ " returns void"
verifyStmt m (Cond pos ex st) = do
  t <- verifyExpr m ex
  unless (isBool t) $ fail $ "Error" ++ showPos pos ++ ": Condition is not of type bool"
  verifyStmt m st
verifyStmt m (CondElse pos ex st st') = do
  t <- verifyExpr m ex
  unless (isBool t) $ fail $ "Error" ++ showPos pos ++ ": Condition is not of type bool"
  verifyStmt m st
  verifyStmt m st'
verifyStmt m (While pos ex st) = do
  t <- verifyExpr m ex
  unless (isBool t) $ fail $ "Error" ++ showPos pos ++ ": Condition is not of type bool"
  verifyStmt m st
verifyStmt m (For pos ty id ex st) = undefined -- Should have been desugared.
verifyStmt m (SExp pos ex) = void $ verifyExpr m ex

isSubtype :: Env -> Type -> Type -> Bool
isSubtype _ (Int _) = isInt
isSubtype _ (Bool _) = isBool
isSubtype _ (Void _) = isVoid
isSubtype _ (Str _) = isStr
isSubtype e (Arr _ ty) = \case
  Arr _ ty' -> isSubtype e ty ty'
  _ -> False
isSubtype e (Cl _ id) = \case
  Cl _ id' ->
    id == id'
      || case classBase (envClasses e Map.! id') of
        Nothing -> False
        Just cl -> isSubtype e (Cl Nothing $ className (envClasses e Map.! id)) (Cl Nothing $ className cl)
  _ -> False

verifyExpr :: Method -> Expr -> EnvM Type
verifyExpr m (EVar pos id) = do
  env <- get
  let (x, y) = fromMaybe (0, 0) pos
  if Map.member id (envInnerVariables env)
    then return $ envInnerVariables env Map.! id
    else
      if Map.member id (envVariables env)
        then return $ envVariables env Map.! id
        else fail $ "Error" ++ showPos pos ++ ": Variable " ++ ident id ++ " is not defined"
verifyExpr m (ELitInt pos n) =
  if n >= -2147483648 && n <= 2147483647
    then return $ Int pos
    else fail $ "Error" ++ showPos pos ++ ": Integer literal is out of range"
verifyExpr m (EString pos s) = return $ Str pos
verifyExpr m (ELitTrue pos) = return $ Bool pos
verifyExpr m (ELitFalse pos) = return $ Bool pos
verifyExpr m (ECastId pos ex) = undefined -- Should have been desugared.
verifyExpr m (ECastArr pos id) = undefined -- Should have been desugared.
verifyExpr m (ECast pos ty) = case ty of
  Cl pos id -> do
    env <- get
    unless (Map.member id (envClasses env)) $ fail $ "Error" ++ showPos pos ++ ": Class " ++ ident id ++ " is not defined"
    return ty
  _ -> do
    when (isArrArr ty) $ fail $ "Error" ++ showPos pos ++ ": Casting to array of arrays is not allowed"
    return ty
verifyExpr m (EFun pos name args) = do
  env <- get
  unless (Map.member name (envFunctions env)) $ fail $ "Error" ++ showPos pos ++ ": Function " ++ ident name ++ " is not defined"
  let f = envFunctions env Map.! name
  unless (length args == length (methodArgs f)) $ fail $ "Error" ++ showPos pos ++ ": Function " ++ ident name ++ " expects " ++ show (length (methodArgs f)) ++ " arguments but got " ++ show (length args)
  let argTypes = map argType (methodArgs f)
  argTypes' <- mapM (verifyExpr m) args
  unless (and $ zipWith (isSubtype env) argTypes argTypes') $ fail $ "Error" ++ showPos pos ++ ": Function " ++ ident name ++ " expects arguments of types " ++ show (map showType argTypes) ++ " but got " ++ show (map showType argTypes')
  return $ methodRetType f
verifyExpr m (EMth pos varexp mth args) = do
  env <- get
  var <- verifyExpr m varexp
  unless (isClass var) $ fail $ "Error" ++ showPos pos ++ ": Expression is not of class type"
  let (Cl _ v) = var
  let cl = envClasses env Map.! v
  let maybeF = getMethod cl mth
  when (isNothing maybeF) $ fail $ "Error" ++ showPos pos ++ ": Class " ++ ident v ++ " does not have method " ++ ident mth
  let Just f = maybeF
  unless (length args == length (methodArgs f)) $ fail $ "Error" ++ showPos pos ++ ": Method " ++ ident mth ++ " expects " ++ show (length (methodArgs f)) ++ " arguments but got " ++ show (length args)
  let argTypes = map argType (methodArgs f)
  argTypes' <- mapM (verifyExpr m) args
  unless (and $ zipWith (isSubtype env) argTypes argTypes') $ fail $ "Error" ++ showPos pos ++ ": Method " ++ ident mth ++ " expects arguments of types " ++ show (showType <$> argTypes) ++ " but got " ++ show (showType <$> argTypes')
  return $ methodRetType f
verifyExpr m (EInd pos ex ex') = do
  t <- verifyExpr m ex
  t' <- verifyExpr m ex'
  env <- get
  case t of
    Arr _ ty -> do
      unless (isInt t') $ fail $ "Error" ++ showPos pos ++ ": Array index is not of type int"
      return ty
    _ -> fail $ "Error" ++ showPos pos ++ ": Expression is not of type array"
verifyExpr m (EAcc pos ex id) = do
  t <- verifyExpr m ex
  env <- get
  case t of
    Cl _ id' -> do
      unless (Map.member id' (envClasses env)) $ fail $ "Error" ++ showPos pos ++ ": Class " ++ ident id' ++ " is not defined"
      let cl = envClasses env Map.! id'
      case getField cl id of
        Nothing -> fail $ "Error" ++ showPos pos ++ ": Class " ++ ident id' ++ " does not have field " ++ ident id
        Just ty -> return ty
    Str _ -> do
      unless (ident id == "length") $ fail $ "Error" ++ showPos pos ++ ": String does not have a field " ++ ident id
      return $ Int pos
    Arr _ _ -> do
      unless (ident id == "length") $ fail $ "Error" ++ showPos pos ++ ": Array does not have a field " ++ ident id
      return $ Int pos
    _ -> fail $ "Error" ++ showPos pos ++ ": " ++ showType t ++ " does not have a field " ++ ident id
verifyExpr m (ENew pos ty) = do
  when (isVoid ty) $ fail $ "Error" ++ showPos pos ++ ": Cannot create an object of type void"
  when (isBool ty) $ fail $ "Error" ++ showPos pos ++ ": Cannot create an object of type bool"
  when (isInt ty) $ fail $ "Error" ++ showPos pos ++ ": Cannot create an object of type int"
  when (isStr ty) $ fail $ "Error" ++ showPos pos ++ ": Cannot create an object of type string"
  return ty
verifyExpr m (ENewArr pos ty ex) = do
  t <- verifyExpr m ex
  when (isArr ty) $ fail $ "Error" ++ showPos pos ++ ": Cannot create an array of arrays"
  when (isVoid ty) $ fail $ "Error" ++ showPos pos ++ ": Cannot create an array of type void"
  unless (isInt t) $ fail $ "Error" ++ showPos pos ++ ": Array size is not of type int"
  return $ Arr pos ty
verifyExpr m (ENeg pos ex) = do
  t <- verifyExpr m ex
  unless (isInt t) $ fail $ "Error" ++ showPos pos ++ ": Negation(-X) is not defined for type " ++ showType t
  return t
verifyExpr m (ENot pos ex) = do
  t <- verifyExpr m ex
  unless (isBool t) $ fail $ "Error" ++ showPos pos ++ ": Negation(~X) is not defined for type " ++ showType t
  return t
verifyExpr m (EMul pos ex _ ex') = verifyIntExpr m pos ex ex' "*" >> return (Int pos)
verifyExpr m (EAdd pos ex _ ex') = do
  t <- verifyExpr m ex
  if isStr t
    then verifyStrExpr m pos ex ex' "+" >> return (Str pos)
    else verifyIntExpr m pos ex ex' "+" >> return (Int pos)
verifyExpr m (ERel pos ex ro ex') = case ro of
  EQU _ -> verifyEqExpr m pos ex ex' "==" >> return (Bool pos)
  NE _ -> verifyEqExpr m pos ex ex' "!=" >> return (Bool pos)
  _ -> verifyIntExpr m pos ex ex' (showRel ro) >> return (Bool pos)
verifyExpr m (EAnd pos ex ex') = verifyBoolExpr m pos ex ex' "&&" >> return (Bool pos)
verifyExpr m (EOr pos ex ex') = verifyBoolExpr m pos ex ex' "||" >> return (Bool pos)

getMethod :: Class -> Ident -> Maybe Method
getMethod cl mth = case Map.lookup mth (classMethods cl) of
  Nothing -> case classBase cl of
    Nothing -> Nothing
    Just p -> getMethod p mth
  Just me -> Just me

getField :: Class -> Ident -> Maybe Type
getField cl fld = case Map.lookup fld (classFields cl) of
  Nothing -> case classBase cl of
    Nothing -> Nothing
    Just p -> getField p fld
  Just ty -> Just ty

argName :: Arg -> Ident
argName (ArgT _ _ id) = id

argType :: Arg -> Type
argType (ArgT _ ty _) = ty

verifyEqExpr :: Method -> BNFC'Position -> Expr -> Expr -> String -> EnvM ()
verifyEqExpr m pos ex ex' op = do
  t <- verifyExpr m ex
  t' <- verifyExpr m ex'
  env <- get
  unless (isSameType t t') $ fail $ "Error" ++ showPos pos ++ ": Type mismatch in " ++ op ++ ". Expected " ++ showType t ++ " but got " ++ showType t'

verifyStrExpr :: Method -> BNFC'Position -> Expr -> Expr -> String -> EnvM ()
verifyStrExpr m pos ex ex' op = do
  t <- verifyExpr m ex
  t' <- verifyExpr m ex'
  env <- get
  unless (isStr t && isStr t') $ fail $ "Error" ++ showPos pos ++ ": Type mismatch in " ++ op ++ ". Expected `string " ++ op ++ " string`, but got `" ++ showType t ++ " " ++ op ++ " " ++ showType t' ++ "`"

verifyIntExpr :: Method -> BNFC'Position -> Expr -> Expr -> String -> EnvM ()
verifyIntExpr m pos ex ex' op = do
  t <- verifyExpr m ex
  t' <- verifyExpr m ex'
  env <- get
  unless (isInt t && isInt t') $ fail $ "Error" ++ showPos pos ++ ": Type mismatch in " ++ op ++ ". Expected `int " ++ op ++ " int`, but got `" ++ showType t ++ " " ++ op ++ " " ++ showType t' ++ "`"

verifyBoolExpr :: Method -> BNFC'Position -> Expr -> Expr -> String -> EnvM ()
verifyBoolExpr m pos ex ex' op = do
  t <- verifyExpr m ex
  t' <- verifyExpr m ex'
  env <- get
  unless (isBool t && isBool t') $ fail $ "Error" ++ showPos pos ++ ": Type mismatch in " ++ op ++ ". Expected `boolean " ++ op ++ " boolean`, but got `" ++ showType t ++ " " ++ op ++ " " ++ showType t' ++ "`"

removeDeadCode :: Env -> Env
removeDeadCode env = env {envFunctions = functions, envClasses = classes}
  where
    functions = Map.map removeDeadCodeFromMethod $ envFunctions env
    classes = Map.map removeDeadCodeFromClass $ envClasses env

removeDeadCodeFromClass :: Class -> Class
removeDeadCodeFromClass cl = cl {classMethods = methods}
  where
    methods = Map.map removeDeadCodeFromMethod $ classMethods cl

removeDeadCodeFromMethod :: Method -> Method
removeDeadCodeFromMethod m = m {methodBody = body}
  where
    (BlockT pos stmts) = methodBody m
    body = BlockT pos $ removeDeadCodeFromStmts stmts

data Simple = T | F | N | M deriving (Eq)

sand :: Simple -> Simple -> Simple
sand T T = T
sand N _ = N
sand _ N = N
sand M s = s
sand s M = s
sand _ _ = F

sor :: Simple -> Simple -> Simple
sor F F = F
sor N _ = N
sor _ N = N
sor M s = s
sor s M = s
sor _ _ = T

snot :: Simple -> Simple
snot T = F
snot F = T
snot s = s

removeDeadCodeFromStmts :: [Stmt] -> [Stmt]
removeDeadCodeFromStmts stmts = map removeDeadCodeFromStmt (aux stmts)
  where
    aux [] = []
    aux (s@(Ret {}) : ss) = [s]
    aux (s@(VRet {}) : ss) = [s]
    aux (s@(Cond pos ex st) : ss) = case simplifyExpr ex of
      T -> st : aux ss
      F -> aux ss
      _ -> s : aux ss
    aux (s@(CondElse pos ex st st') : ss) = case simplifyExpr ex of
      T -> st : aux ss
      F -> st' : aux ss
      _ -> s : aux ss
    aux (s@(While pos ex st) : ss) = case simplifyExpr ex of
      T -> [s]
      F -> aux ss
      _ -> s : aux ss
    aux (s : ss) = s : aux ss
    removeDeadCodeFromStmt (BStmt p1 (BlockT p2 stmts)) = BStmt p1 (BlockT p2 $ removeDeadCodeFromStmts stmts)
    removeDeadCodeFromStmt (Cond pos ex st) = Cond pos ex $ removeDeadCodeFromStmt st
    removeDeadCodeFromStmt (CondElse pos ex st st') = CondElse pos ex (removeDeadCodeFromStmt st) (removeDeadCodeFromStmt st')
    removeDeadCodeFromStmt (While pos ex st) = While pos ex $ removeDeadCodeFromStmt st
    removeDeadCodeFromStmt s = s

simplifyExpr :: Expr -> Simple
simplifyExpr (ELitTrue ma) = T
simplifyExpr (ELitFalse ma) = F
simplifyExpr (EFun ma id exs) = N
simplifyExpr (EMth ma ex id exs) = N
simplifyExpr (EInd ma ex ex') = sand (simplifyExpr ex) (simplifyExpr ex')
simplifyExpr (EAcc ma ex id) = simplifyExpr ex
simplifyExpr (ENewArr ma ty ex) = simplifyExpr ex
simplifyExpr (ENeg ma ex) = simplifyExpr ex
simplifyExpr (ENot ma ex) = snot $ simplifyExpr ex
simplifyExpr (EMul ma ex mo ex') = sand (simplifyExpr ex) (simplifyExpr ex')
simplifyExpr (EAdd ma ex ao ex') = sand (simplifyExpr ex) (simplifyExpr ex')
simplifyExpr (ERel ma ex ro ex') = case sand (simplifyExpr ex) (simplifyExpr ex') of
  N -> N
  _ -> case ro of
    EQU _ -> exprEq ex ex'
    NE _ -> snot $ exprEq ex ex'
    _ -> M
simplifyExpr (EAnd ma ex ex') = sand (simplifyExpr ex) (simplifyExpr ex')
simplifyExpr (EOr ma ex ex') = sor (simplifyExpr ex) (simplifyExpr ex')
simplifyExpr _ = M

exprEq :: Expr -> Expr -> Simple
exprEq (EVar _ id) (EVar _ id') = if id == id' then T else M
exprEq (ELitInt _ n) (ELitInt _ n') = if n == n' then T else M
exprEq (EString _ s) (EString _ s') = if s == s' then T else M
exprEq (ELitTrue _) (ELitTrue _) = T
exprEq (ELitFalse _) (ELitFalse _) = T
exprEq (ECastId _ ex) (ECastId _ ex') = undefined -- Should have been desugared
exprEq (ECastArr _ id) (ECastArr _ id') = undefined -- Should have been desugared
exprEq (ECast _ ty) (ECast _ ty') = if isSameType ty ty' then T else M
exprEq (EInd _ ex ex') (EInd _ ex'' ex''') = sand (exprEq ex ex'') (exprEq ex' ex''')
exprEq (EAcc _ ex id) (EAcc _ ex' id') = if id == id' then exprEq ex ex' else M
exprEq (ENew _ ty) (ENew _ ty') = F
exprEq (ENewArr _ ty ex) (ENewArr _ ty' ex') = F
exprEq (ENeg _ ex) (ENeg _ ex') = exprEq ex ex'
exprEq (ENot _ ex) (ENot _ ex') = exprEq ex ex'
exprEq (EMul _ ex mo ex') (EMul _ ex'' mo' ex''') = if mulOpEq mo mo' then sand (exprEq ex ex'') (exprEq ex' ex''') else M
exprEq (EAdd _ ex ao ex') (EAdd _ ex'' ao' ex''') = if addOpEq ao ao' then sand (exprEq ex ex'') (exprEq ex' ex''') else M
exprEq (ERel _ ex ro ex') (ERel _ ex'' ro' ex''') = if relOpEq ro ro' then sand (exprEq ex ex'') (exprEq ex' ex''') else M
exprEq (EAnd _ ex ex') (EAnd _ ex'' ex''') = (exprEq ex ex'' `sand` exprEq ex' ex''') `sor` (exprEq ex ex''' `sand` exprEq ex' ex'')
exprEq (EOr _ ex ex') (EOr _ ex'' ex''') = (exprEq ex ex'' `sand` exprEq ex' ex''') `sor` (exprEq ex ex''' `sand` exprEq ex' ex'')
exprEq _ _ = M

assocExprEq :: (Expr, Expr) -> (Expr, Expr) -> Simple
assocExprEq (ex, ex') (ex'', ex''') = (exprEq ex ex'' `sand` exprEq ex' ex''') `sor` (exprEq ex ex''' `sand` exprEq ex' ex''')

checkReturns :: Env -> Either String ()
checkReturns env = do
  let funs =
        filter (not . flip Set.member (Map.keysSet builtinMethods) . methodName) $
          filter (not . isVoid . methodRetType) $
            map snd $
              Map.assocs $
                envFunctions env
  let methods =
        filter (not . isVoid . methodRetType) $
          map snd $
            concatMap (Map.assocs . classMethods . snd) (Map.assocs $ envClasses env)
  forM_
    funs
    ( \f ->
        unless (hasReturn (methodBody f)) $
          fail $
            "Error: Function " ++ ident (methodName f) ++ " does not return a value"
    )
  forM_
    methods
    ( \f ->
        let Right cl = methodThis f
         in unless (hasReturn (methodBody f)) $
              fail $
                "Error: Method " ++ ident (methodName f) ++ " of class " ++ ident (className cl) ++ " does not return a value"
    )

hasReturn :: Block -> Bool
hasReturn (BlockT _ []) = False
hasReturn (BlockT _ stmts) = aux $ last stmts
  where
    aux (Ret _ _) = True
    aux (BStmt _ b) = hasReturn b
    aux (CondElse _ _ b b') = hasReturn (BlockT Nothing [b]) || hasReturn (BlockT Nothing [b'])
    aux (While _ _ b) = hasReturn (BlockT Nothing [b])
    aux _ = False

ident :: Ident -> String
ident (Ident s) = s

showPos :: BNFC'Position -> String
showPos (Just (a, b)) = "(line " ++ show a ++ ", column " ++ show b ++ ")"
showPos Nothing = error "Error: Position not found"

showRel :: RelOp -> String
showRel (LTH _) = "<"
showRel (LE _) = "<="
showRel (GTH _) = ">"
showRel (GE _) = ">="
showRel (EQU _) = "=="
showRel (NE _) = "!="

relOpEq :: RelOp -> RelOp -> Bool
relOpEq (EQU _) (EQU _) = True
relOpEq (NE _) (NE _) = True
relOpEq (LTH _) (LTH _) = True
relOpEq (LE _) (LE _) = True
relOpEq (GTH _) (GTH _) = True
relOpEq (GE _) (GE _) = True
relOpEq _ _ = False

mulOpEq :: MulOp -> MulOp -> Bool
mulOpEq (Times _) (Times _) = True
mulOpEq (Div _) (Div _) = True
mulOpEq (Mod _) (Mod _) = True
mulOpEq _ _ = False

addOpEq :: AddOp -> AddOp -> Bool
addOpEq (Plus _) (Plus _) = True
addOpEq (Minus _) (Minus _) = True
addOpEq _ _ = False

showType :: Type -> String
showType (Int _) = "int"
showType (Bool _) = "boolean"
showType (Str _) = "string"
showType (Void _) = "void"
showType (Arr _ ty) = showType ty ++ "[]"
showType (Cl _ id) = ident id

isSameType :: Type -> Type -> Bool
isSameType (Void _) (Void _) = True
isSameType (Int _) (Int _) = True
isSameType (Bool _) (Bool _) = True
isSameType (Str _) (Str _) = True
isSameType (Cl _ id) (Cl _ id') = id == id'
isSameType (Arr _ t) (Arr _ t') = isSameType t t'
isSameType _ _ = False

isVoid :: Type -> Bool
isVoid t = isSameType t (Void Nothing)

isInt :: Type -> Bool
isInt t = isSameType t (Int Nothing)

isBool :: Type -> Bool
isBool t = isSameType t (Bool Nothing)

isStr :: Type -> Bool
isStr t = isSameType t (Str Nothing)

isArr :: Type -> Bool
isArr (Arr _ _) = True
isArr _ = False

isArrArr :: Type -> Bool
isArrArr (Arr _ (Arr _ _)) = True
isArrArr _ = False

isClass :: Type -> Bool
isClass (Cl _ _) = True
isClass _ = False

forbiddenTypes :: Set Ident
forbiddenTypes = Set.fromList [Ident "int", Ident "boolean", Ident "string", Ident "void"]

forbiddenVars :: Set Ident
forbiddenVars = Set.fromList [Ident "self", Ident "true", Ident "false"]

removeBulitinMethods :: Env -> Env
removeBulitinMethods env =
  env
    { envFunctions =
        Map.filterWithKey (\k _ -> not $ Set.member k (Map.keysSet builtinMethods)) (envFunctions env)
    }

builtinMethods :: Map.Map Ident Method
builtinMethods =
  Map.fromList
    [ (Ident "printInt", Method (Ident "printInt") (Void Nothing) (Left $ Ident "") [ArgT Nothing (Int Nothing) (Ident "x")] (BlockT Nothing [])),
      (Ident "printString", Method (Ident "printString") (Void Nothing) (Left $ Ident "") [ArgT Nothing (Str Nothing) (Ident "x")] (BlockT Nothing [])),
      (Ident "error", Method (Ident "error") (Void Nothing) (Left $ Ident "") [] (BlockT Nothing [])),
      (Ident "readInt", Method (Ident "readInt") (Int Nothing) (Left $ Ident "") [] (BlockT Nothing [])),
      (Ident "readString", Method (Ident "readString") (Str Nothing) (Left $ Ident "") [] (BlockT Nothing [])),
      (Ident "concatStrings", Method (Ident "concatStrings") (Str Nothing) (Left $ Ident "") [ArgT Nothing (Str Nothing) (Ident "x"), ArgT Nothing (Str Nothing) (Ident "y")] (BlockT Nothing [])),
      (Ident "compareStrings", Method (Ident "compareStrings") (Bool Nothing) (Left $ Ident "") [ArgT Nothing (Str Nothing) (Ident "x"), ArgT Nothing (Str Nothing) (Ident "y")] (BlockT Nothing []))
    ]
