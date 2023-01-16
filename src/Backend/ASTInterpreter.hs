module Backend.ASTInterpreter where

import Backend.Milkremover
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, fromJust)
import Control.Monad (foldM, void)
import Data.List (elemIndex)


interpret :: Espresso -> IO ()
interpret (Espresso functions) = void (executeFun functions (functions Map.!   "main") Map.empty)

executeFun :: Map.Map Label Method -> Method -> Map.Map Label Value -> IO Value
executeFun funs (Method _ body _ _) env = do
    ret <- foldM (executeBlock body funs) env body
    return $ fromMaybe (VInt 0) (ret Map.!? "ret")

executeBlock :: EspressoBlock -> Map.Map Label Method -> Map.Map Label Value -> Instruction -> IO (Map.Map Label Value)
executeBlock eb funs env instr = if "ret" `Map.member` env then return env else case instr of
  ADD ls lv lv' -> do
    v <- getVal env lv
    v' <- getVal env lv'
    case (v, v') of
      (VInt n, VInt n') -> return $ Map.insert ls (VInt (n + n')) env
      (VString s, VString s') -> return $ Map.insert ls (VString (s ++ s')) env
      _ -> error "Type error"
  SUB s lv lv' -> do
    v <- getVal env lv
    v' <- getVal env lv'
    case (v, v') of
      (VInt n, VInt n') -> return $ Map.insert s (VInt (n - n')) env
      _ -> error "Type error"
  MUL s lv lv' -> do
    v <- getVal env lv
    v' <- getVal env lv'
    case (v, v') of
      (VInt n, VInt n') -> return $ Map.insert s (VInt (n * n')) env
      _ -> error "Type error"
  DIV s lv lv' -> do
    v <- getVal env lv
    v' <- getVal env lv'
    case (v, v') of
      (VInt n, VInt n') -> return $ Map.insert s (VInt (n `div` n')) env
      _ -> error "Type error"
  MOD s lv lv' -> do
    v <- getVal env lv
    v' <- getVal env lv'
    case (v, v') of
      (VInt n, VInt n') -> return $ Map.insert s (VInt (n `mod` n')) env
      _ -> error "Type error"
  AND s lv lv' -> do
    v <- getVal env lv
    v' <- getVal env lv'
    case (v, v') of
      (VInt b, VInt b') -> return $ Map.insert s (VInt (if b == 1 && b' == 1 then 1 else 0)) env
      _ -> error "Type error"
  OR s lv lv' -> do
    v <- getVal env lv
    v' <- getVal env lv'
    case (v, v') of
      (VInt b, VInt b') -> return $ Map.insert s (VInt (if b == 1 || b' == 1 then 1 else 0)) env
      _ -> error "Type error"
  LRT s lv lv' -> cmpaux s lv lv' (<)
  GRT s lv lv' -> cmpaux s lv lv' (>)
  LRE s lv lv' -> cmpaux s lv lv' (<=)
  GRE s lv lv' -> cmpaux s lv lv' (>=)
  EQS s lv lv' -> do
    v <- getVal env lv
    v' <- getVal env lv'
    case (v, v') of
      (VInt n, VInt n') -> return $ Map.insert s (VBool (n == n')) env
      (VString s, VString s') -> return $ Map.insert s (VBool (s == s')) env
      (VBool b, VBool b') -> return $ Map.insert s (VBool (b == b')) env
      _ -> error "Type error"
  NEQ s lv lv' -> do
    v <- getVal env lv
    v' <- getVal env lv'
    case (v, v') of
      (VInt n, VInt n') -> return $ Map.insert s (VBool (n /= n')) env
      (VString s, VString s') -> return $ Map.insert s (VBool (s /= s')) env
      (VBool b, VBool b') -> return $ Map.insert s (VBool (b /= b')) env
      _ -> error "Type error"
  CBR v lt lf -> do
    boo <- getVal env v
    case boo of
      VBool b -> executeBlock eb funs env (BR (if b then lt else lf))
      _ -> error "Type error"
  NEG s lv -> do
    v <- getVal env lv
    case v of
      VInt n -> return $ Map.insert s (VInt (-n)) env
      _ -> error "Type error"
  NOT s lv -> do
    v <- getVal env lv
    case v of
      VBool b -> return $ Map.insert s (VBool (not b)) env
      _ -> error "Type error"
  CPY s lv -> do
    v <- getVal env lv
    return $ Map.insert s v env
  PHI s ls -> undefined
  BR s -> do
    let pos = fromJust $ elemIndex (LAB s) eb
    r <- foldM (executeBlock eb funs) env (drop (pos + 1) eb)
    if "ret" `Map.member` r then return r else return $ Map.insert "ret" (VInt 0) r
  CALL s str args -> do
    let (Method argNames body _ _) = funs Map.!   str
    vals <- mapM (getVal env) args
    let namedArgs = zip argNames vals
    let env' = Map.fromList namedArgs
    v <- case str of
        "printInt" -> print (head vals) >> return (VInt 0)
        "readInt" -> VInt <$> readLn
        "printString" -> print (head vals) >> return (VInt 0)
        "readString" -> VString <$> getLine
        "concatStrings" -> return $ VString $ concatMap (\(VString s) -> s) vals
        "compareStrings" -> return $ VBool $ head vals == last vals
        "error" -> undefined
        _ -> executeFun funs (Method argNames body Map.empty EVoid) env'
    return $ Map.insert s v env
  RET lv -> do
    v <- getVal env lv
    return $ Map.insert "ret" v env
  VRET -> return $ Map.insert "ret" (VInt 0) env
  LAB s -> return env
  where
    cmpaux s lv lv' f = do
      v <- getVal env lv
      v' <- getVal env lv'
      case (v, v') of
        (VInt n, VInt n') -> return $ Map.insert s (VBool (f n n')) env
        _ -> error "Type error"
