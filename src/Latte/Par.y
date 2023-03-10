-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.4).

-- Parser definition for use with Happy
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Latte.Par
  ( happyError
  , myLexer
  , pProgram
  ) where

import Prelude

import qualified Latte.Abs
import Latte.Lex

}

%name pProgram_internal Program
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '!'       { PT _ (TS _ 1)  }
  '!='      { PT _ (TS _ 2)  }
  '%'       { PT _ (TS _ 3)  }
  '&&'      { PT _ (TS _ 4)  }
  '('       { PT _ (TS _ 5)  }
  ')'       { PT _ (TS _ 6)  }
  '*'       { PT _ (TS _ 7)  }
  '+'       { PT _ (TS _ 8)  }
  '++'      { PT _ (TS _ 9)  }
  ','       { PT _ (TS _ 10) }
  '-'       { PT _ (TS _ 11) }
  '--'      { PT _ (TS _ 12) }
  '.'       { PT _ (TS _ 13) }
  '/'       { PT _ (TS _ 14) }
  ':'       { PT _ (TS _ 15) }
  ';'       { PT _ (TS _ 16) }
  '<'       { PT _ (TS _ 17) }
  '<='      { PT _ (TS _ 18) }
  '='       { PT _ (TS _ 19) }
  '=='      { PT _ (TS _ 20) }
  '>'       { PT _ (TS _ 21) }
  '>='      { PT _ (TS _ 22) }
  '['       { PT _ (TS _ 23) }
  '[]'      { PT _ (TS _ 24) }
  ']'       { PT _ (TS _ 25) }
  'boolean' { PT _ (TS _ 26) }
  'class'   { PT _ (TS _ 27) }
  'else'    { PT _ (TS _ 28) }
  'extends' { PT _ (TS _ 29) }
  'false'   { PT _ (TS _ 30) }
  'for'     { PT _ (TS _ 31) }
  'if'      { PT _ (TS _ 32) }
  'int'     { PT _ (TS _ 33) }
  'new'     { PT _ (TS _ 34) }
  'null'    { PT _ (TS _ 35) }
  'return'  { PT _ (TS _ 36) }
  'string'  { PT _ (TS _ 37) }
  'true'    { PT _ (TS _ 38) }
  'void'    { PT _ (TS _ 39) }
  'while'   { PT _ (TS _ 40) }
  '{'       { PT _ (TS _ 41) }
  '||'      { PT _ (TS _ 42) }
  '}'       { PT _ (TS _ 43) }
  L_Ident   { PT _ (TV _)    }
  L_integ   { PT _ (TI _)    }
  L_quoted  { PT _ (TL _)    }

%%

Ident :: { (Latte.Abs.BNFC'Position, Latte.Abs.Ident) }
Ident  : L_Ident { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Ident (tokenText $1)) }

Integer :: { (Latte.Abs.BNFC'Position, Integer) }
Integer  : L_integ  { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), (read (tokenText $1)) :: Integer) }

String  :: { (Latte.Abs.BNFC'Position, String) }
String   : L_quoted { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), ((\(PT _ (TL s)) -> s) $1)) }

Program :: { (Latte.Abs.BNFC'Position, Latte.Abs.Program) }
Program
  : ListTopDef { (fst $1, Latte.Abs.ProgramT (fst $1) (snd $1)) }

TopDef :: { (Latte.Abs.BNFC'Position, Latte.Abs.TopDef) }
TopDef
  : Type Ident '(' ListArg ')' Block { (fst $1, Latte.Abs.FnDef (fst $1) (snd $1) (snd $2) (snd $4) (snd $6)) }
  | 'class' Ident ClBlock { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ClDef (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $3)) }
  | 'class' Ident 'extends' Ident ClBlock { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.SubClDef (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $4) (snd $5)) }

ListTopDef :: { (Latte.Abs.BNFC'Position, [Latte.Abs.TopDef]) }
ListTopDef
  : TopDef { (fst $1, (:[]) (snd $1)) }
  | TopDef ListTopDef { (fst $1, (:) (snd $1) (snd $2)) }

Arg :: { (Latte.Abs.BNFC'Position, Latte.Abs.Arg) }
Arg
  : Type Ident { (fst $1, Latte.Abs.ArgT (fst $1) (snd $1) (snd $2)) }

ListArg :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Arg]) }
ListArg
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | Arg { (fst $1, (:[]) (snd $1)) }
  | Arg ',' ListArg { (fst $1, (:) (snd $1) (snd $3)) }

ClBlock :: { (Latte.Abs.BNFC'Position, Latte.Abs.ClBlock) }
ClBlock
  : '{' ListInClDef '}' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ClBlockT (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }

InClDef :: { (Latte.Abs.BNFC'Position, Latte.Abs.InClDef) }
InClDef
  : Type Ident '(' ListArg ')' Block { (fst $1, Latte.Abs.MthDef (fst $1) (snd $1) (snd $2) (snd $4) (snd $6)) }
  | Type Ident ';' { (fst $1, Latte.Abs.FldDef (fst $1) (snd $1) (snd $2)) }

ListInClDef :: { (Latte.Abs.BNFC'Position, [Latte.Abs.InClDef]) }
ListInClDef
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | InClDef ListInClDef { (fst $1, (:) (snd $1) (snd $2)) }

Block :: { (Latte.Abs.BNFC'Position, Latte.Abs.Block) }
Block
  : '{' ListStmt '}' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.BlockT (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }

ListStmt :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Stmt]) }
ListStmt
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | Stmt ListStmt { (fst $1, (:) (snd $1) (snd $2)) }

Stmt :: { (Latte.Abs.BNFC'Position, Latte.Abs.Stmt) }
Stmt
  : ';' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Empty (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | Block { (fst $1, Latte.Abs.BStmt (fst $1) (snd $1)) }
  | Type ListItem ';' { (fst $1, Latte.Abs.Decl (fst $1) (snd $1) (snd $2)) }
  | Expr '=' Expr ';' { (fst $1, Latte.Abs.Ass (fst $1) (snd $1) (snd $3)) }
  | Ident '++' ';' { (fst $1, Latte.Abs.Incr (fst $1) (snd $1)) }
  | Ident '--' ';' { (fst $1, Latte.Abs.Decr (fst $1) (snd $1)) }
  | 'return' Expr ';' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Ret (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | 'return' ';' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.VRet (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | 'if' '(' Expr ')' Stmt { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Cond (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5)) }
  | 'if' '(' Expr ')' Stmt 'else' Stmt { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.CondElse (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5) (snd $7)) }
  | 'while' '(' Expr ')' Stmt { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.While (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5)) }
  | 'for' '(' Type Ident ':' Expr ')' Stmt { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.For (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $4) (snd $6) (snd $8)) }
  | Expr ';' { (fst $1, Latte.Abs.SExp (fst $1) (snd $1)) }

Item :: { (Latte.Abs.BNFC'Position, Latte.Abs.Item) }
Item
  : Ident { (fst $1, Latte.Abs.NoInit (fst $1) (snd $1)) }
  | Ident '=' Expr { (fst $1, Latte.Abs.Init (fst $1) (snd $1) (snd $3)) }

ListItem :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Item]) }
ListItem
  : Item { (fst $1, (:[]) (snd $1)) }
  | Item ',' ListItem { (fst $1, (:) (snd $1) (snd $3)) }

Type :: { (Latte.Abs.BNFC'Position, Latte.Abs.Type) }
Type
  : 'int' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Int (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | 'boolean' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Bool (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | 'void' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Void (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | 'string' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Str (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | Type '[]' { (fst $1, Latte.Abs.Arr (fst $1) (snd $1)) }
  | Ident { (fst $1, Latte.Abs.Cl (fst $1) (snd $1)) }

ListType :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Type]) }
ListType
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | Type { (fst $1, (:[]) (snd $1)) }
  | Type ',' ListType { (fst $1, (:) (snd $1) (snd $3)) }

Expr7 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr7
  : Ident { (fst $1, Latte.Abs.EVar (fst $1) (snd $1)) }
  | Integer { (fst $1, Latte.Abs.ELitInt (fst $1) (snd $1)) }
  | String { (fst $1, Latte.Abs.EString (fst $1) (snd $1)) }
  | 'true' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ELitTrue (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | 'false' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ELitFalse (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '(' Expr ')' 'null' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ECastId (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | '(' Type '[]' ')' 'null' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ECastArr (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | Ident '(' ListExpr ')' { (fst $1, Latte.Abs.EFun (fst $1) (snd $1) (snd $3)) }
  | Expr7 '.' Ident '(' ListExpr ')' { (fst $1, Latte.Abs.EMth (fst $1) (snd $1) (snd $3) (snd $5)) }
  | Expr7 '[' Expr ']' { (fst $1, Latte.Abs.EInd (fst $1) (snd $1) (snd $3)) }
  | Expr7 '.' Ident { (fst $1, Latte.Abs.EAcc (fst $1) (snd $1) (snd $3)) }
  | Expr8 { (fst $1, (snd $1)) }

Expr6 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr6
  : 'new' Type { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ENew (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | 'new' Type '[' Expr ']' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ENewArr (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $4)) }
  | Expr7 { (fst $1, (snd $1)) }

Expr5 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr5
  : '-' Expr6 { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ENeg (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | '!' Expr6 { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ENot (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | Expr6 { (fst $1, (snd $1)) }

Expr4 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr4
  : Expr4 MulOp Expr5 { (fst $1, Latte.Abs.EMul (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr5 { (fst $1, (snd $1)) }

Expr3 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr3
  : Expr3 AddOp Expr4 { (fst $1, Latte.Abs.EAdd (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr4 { (fst $1, (snd $1)) }

Expr2 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr2
  : Expr2 RelOp Expr3 { (fst $1, Latte.Abs.ERel (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr3 { (fst $1, (snd $1)) }

Expr1 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr1
  : Expr2 '&&' Expr1 { (fst $1, Latte.Abs.EAnd (fst $1) (snd $1) (snd $3)) }
  | Expr2 { (fst $1, (snd $1)) }

Expr :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr
  : Expr1 '||' Expr { (fst $1, Latte.Abs.EOr (fst $1) (snd $1) (snd $3)) }
  | Expr1 { (fst $1, (snd $1)) }

Expr8 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr8
  : '(' Expr ')' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), (snd $2)) }

ListExpr :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Expr]) }
ListExpr
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | Expr { (fst $1, (:[]) (snd $1)) }
  | Expr ',' ListExpr { (fst $1, (:) (snd $1) (snd $3)) }

AddOp :: { (Latte.Abs.BNFC'Position, Latte.Abs.AddOp) }
AddOp
  : '+' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Plus (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '-' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Minus (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }

MulOp :: { (Latte.Abs.BNFC'Position, Latte.Abs.MulOp) }
MulOp
  : '*' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Times (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '/' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Div (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '%' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Mod (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }

RelOp :: { (Latte.Abs.BNFC'Position, Latte.Abs.RelOp) }
RelOp
  : '<' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.LTH (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '<=' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.LE (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '>' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.GTH (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '>=' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.GE (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '==' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.EQU (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '!=' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.NE (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }

{

type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

-- Entrypoints

pProgram :: [Token] -> Err Latte.Abs.Program
pProgram = fmap snd . pProgram_internal
}

