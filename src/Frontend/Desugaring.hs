module Frontend.Desugaring where

import Data.Functor ((<&>))
import Latte.Abs
  ( AddOp' (..),
    BNFC'Position,
    Block,
    Block' (BlockT),
    ClBlock,
    ClBlock' (ClBlockT),
    Expr,
    Expr' (..),
    Ident (..),
    InClDef,
    InClDef' (MthDef),
    Item,
    Item' (..),
    MulOp' (..),
    Program,
    Program' (ProgramT),
    RelOp,
    RelOp' (..),
    Stmt,
    Stmt' (..),
    TopDef,
    TopDef' (..),
    Type,
    Type' (..),
  )
import Latte.Skel (Err)

-- deconstructs foreach loops
-- deconstructs i++ and i--
-- inserts { } into if else expressions
-- evaluate trivial constexprs
desugar :: Program -> Err Program
desugar (ProgramT x tds) = mapM desugarTopDefs tds <&> ProgramT x

desugarTopDefs :: TopDef -> Err TopDef
desugarTopDefs (FnDef pos t name args block) = desugarBlock block <&> FnDef pos t name args
desugarTopDefs (ClDef pos name block) = desugarClassBlock block <&> ClDef pos name
desugarTopDefs (SubClDef pos name pname block) = desugarClassBlock block <&> SubClDef pos name pname

desugarBlock :: Block -> Err Block
desugarBlock (BlockT pos stmts) = mapM desugarStmt stmts <&> BlockT pos

desugarClassBlock :: ClBlock -> Err ClBlock
desugarClassBlock (ClBlockT pos clDefs) = mapM desugarInnerClassDef clDefs <&> ClBlockT pos

desugarStmt :: Stmt -> Err Stmt
desugarStmt (BStmt pos block) = desugarBlock block <&> BStmt pos
desugarStmt (Decl pos t items) = mapM desugarItem items <&> Decl pos t
desugarStmt (Ass pos e1 e2) = do
  e1' <- desugarExpr e1
  e2' <- desugarExpr e2
  return (Ass pos e1' e2')
desugarStmt (Incr pos name) = return $ Ass pos (EVar pos name) (EAdd pos (EVar pos name) (Plus pos) (ELitInt pos 1))
desugarStmt (Decr pos name) = return $ Ass pos (EVar pos name) (EAdd pos (EVar pos name) (Minus pos) (ELitInt pos 1))
desugarStmt (Ret pos e) = desugarExpr e <&> Ret pos
desugarStmt (Cond pos e s) = do
  e' <- desugarExpr e
  s' <- desugarStmt s
  return (Cond pos e' (wrapBlock s'))
desugarStmt (CondElse pos e s1 s2) = do
  e' <- desugarExpr e
  s1' <- desugarStmt s1
  s2' <- desugarStmt s2
  return (CondElse pos e' (wrapBlock s1') (wrapBlock s2'))
desugarStmt (While pos e s) = do
  e' <- desugarExpr e
  s' <- desugarStmt s
  return (While pos e' (wrapBlock s'))
desugarStmt (SExp pos e) = desugarExpr e <&> SExp pos
desugarStmt (For pos t name e s) = do
  e' <- desugarExpr e
  s' <- desugarStmt s
  let arr = Decl pos (Arr pos t) [Init pos (Ident "@arr") e']
  let idx = Decl pos (Int pos) [Init pos (Ident "@idx") (ELitInt pos 0)]
  let av = EVar pos (Ident "@arr")
  let iv = EVar pos (Ident "@idx")
  let lgh = EAcc pos av (Ident "length")
  let elem = Decl pos t [Init pos name (EInd pos av iv)]
  let inc = Ass pos (EVar pos (Ident "@idx")) (EAdd pos (EVar pos (Ident "@idx")) (Plus pos) (ELitInt pos 1))
  return $
    BStmt pos $
      BlockT
        pos
        [ arr,
          idx,
          While pos (ERel pos (ELitInt pos 0) (LTH pos) iv) $
            BStmt pos $
              BlockT
                pos
                [ elem,
                  s',
                  inc
                ]
        ]
-- Empty, VRet
desugarStmt x = return x

desugarInnerClassDef :: InClDef -> Err InClDef
desugarInnerClassDef (MthDef pos t name args block) = desugarBlock block <&> MthDef pos t name args
desugarInnerClassDef x = return x

desugarItem :: Item -> Err Item
desugarItem (Init pos name e) = desugarExpr e <&> Init pos name
desugarItem x = return x

desugarExpr :: Expr -> Err Expr
desugarExpr e = do
  e' <- case e of
    ECastId pos (EVar p name) -> do
      let t = case name of
            Ident "int" -> Int pos
            Ident "string" -> Str pos
            Ident "boolean" -> Bool pos
            Ident "void" -> Void pos
            _ -> Cl pos name
      return $ ECast pos t
    ECastId pos _ -> Left $ "Error: Illegal cast at " ++ showPos pos
    ECastArr pos ty -> return $ ECast pos (Arr pos ty)
    EFun pos id es -> do
      es' <- mapM desugarExpr es
      return $ EFun pos id es'
    EMth pos cl id es -> do
      cl' <- desugarExpr cl
      es' <- mapM desugarExpr es
      return $ EMth pos cl' id es'
    EInd pos e1 e2 -> do
      e1' <- desugarExpr e1
      e2' <- desugarExpr e2
      return $ EInd pos e1' e2'
    EAcc pos e1 i -> do
      e1' <- desugarExpr e1
      return $ EAcc pos e1' i
    ENewArr pos t e1 -> desugarExpr e1 <&> ENewArr pos t
    ENeg pos e1 -> desugarExpr e1 <&> ENeg pos
    ENot pos e1 -> desugarExpr e1 <&> ENot pos
    EMul pos e1 op e2 -> do
      e1' <- desugarExpr e1
      e2' <- desugarExpr e2
      return $ EMul pos e1' op e2'
    EAdd pos e1 op e2 -> do
      e1' <- desugarExpr e1
      e2' <- desugarExpr e2
      return $ EAdd pos e1' op e2'
    ERel pos e1 op e2 -> do
      e1' <- desugarExpr e1
      e2' <- desugarExpr e2
      return $ ERel pos e1' op e2'
    EAnd pos e1 e2 -> do
      e1' <- desugarExpr e1
      e2' <- desugarExpr e2
      return $ EAnd pos e1' e2'
    EOr pos e1 e2 -> do
      e1' <- desugarExpr e1
      e2' <- desugarExpr e2
      return $ EOr pos e1' e2'
    _ -> return e
  return $ constexpr e'

showPos :: BNFC'Position -> String
showPos (Just (a, b)) = "line " ++ show a ++ ", column " ++ show b
showPos Nothing = error "Error: Position not found"

constexpr :: Expr -> Expr
constexpr (ENeg pos (ELitInt _ v)) = ELitInt pos (-v)
constexpr e@(ENot pos e1) = case e1 of
  ELitTrue _ -> ELitFalse pos
  ELitFalse _ -> ELitTrue pos
  _ -> e
constexpr (EMul pos (ELitInt _ n1) op (ELitInt _ n2)) = case op of
  Times _ -> ELitInt pos $ n1 * n2
  Div _ -> ELitInt pos $ n1 `div` n2
  Mod _ -> ELitInt pos $ n1 `mod` n2
constexpr (EAdd pos (ELitInt _ n1) op (ELitInt _ n2)) = case op of
  Plus _ -> ELitInt pos $ n1 + n2
  Minus _ -> ELitInt pos $ n1 - n2
constexpr e@(ERel pos e1 op e2) = case (e1, e2) of
  (EVar _ v1, EVar _ v2) | v1 == v2 -> case op of
    LTH _ -> ELitFalse pos
    LE _ -> ELitTrue pos
    GTH _ -> ELitFalse pos
    GE _ -> ELitTrue pos
    EQU _ -> ELitTrue pos
    NE _ -> ELitFalse pos
  (ELitInt _ v1, ELitInt _ v2) -> evalOrdering pos v1 v2 op
  (EString _ v1, EString _ v2) -> evalOrdering pos v1 v2 op
  (ELitTrue _, ELitTrue _) -> evalOrdering pos True True op
  (ELitTrue _, ELitFalse _) -> evalOrdering pos True False op
  (ELitFalse _, ELitTrue _) -> evalOrdering pos False True op
  (ELitFalse _, ELitFalse _) -> evalOrdering pos False False op
  (ECast {}, ECast {}) -> case op of
    EQU _ -> ELitTrue pos
    NE _ -> ELitFalse pos
    _ -> e
  _ -> e
constexpr e@(EAnd pos e1 e2) = case (e1, e2) of
  (ELitFalse _, ELitTrue _) -> ELitFalse pos
  (ELitTrue _, ELitFalse _) -> ELitFalse pos
  (ELitFalse _, ELitFalse _) -> ELitFalse pos
  (ELitTrue _, ELitTrue _) -> ELitTrue pos
  _ -> e
constexpr e@(EOr pos e1 e2) = case (e1, e2) of
  (ELitFalse _, ELitTrue _) -> ELitTrue pos
  (ELitTrue _, ELitFalse _) -> ELitTrue pos
  (ELitFalse _, ELitFalse _) -> ELitFalse pos
  (ELitTrue _, ELitTrue _) -> ELitTrue pos
  _ -> e
constexpr e = e

evalOrdering :: Ord a => BNFC'Position -> a -> a -> RelOp -> Expr
evalOrdering pos a b op =
  if case op of
    LTH _ -> a < b
    LE _ -> a <= b
    GTH _ -> a > b
    GE _ -> a >= b
    EQU _ -> a == b
    NE _ -> a /= b
    then ELitTrue pos
    else ELitFalse pos

wrapBlock :: Stmt -> Stmt
wrapBlock s@(BStmt _ _) = s
wrapBlock s = let pos = getPos s in BStmt pos (BlockT pos [s])

getPos :: Stmt -> BNFC'Position
getPos (BStmt pos _) = pos
getPos (Decl pos _ _) = pos
getPos (Ass pos _ _) = pos
getPos (Incr pos _) = pos
getPos (Decr pos _) = pos
getPos (Ret pos _) = pos
getPos (Cond pos _ _) = pos
getPos (CondElse pos _ _ _) = pos
getPos (While pos _ _) = pos
getPos (SExp pos _) = pos
getPos (For pos _ _ _ _) = pos
getPos (Empty pos) = pos
getPos (VRet pos) = pos