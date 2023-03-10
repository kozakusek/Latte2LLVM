-- File generated by the BNF Converter (bnfc 2.9.4).

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The abstract syntax of language Latte.

module Latte.Abs where

import Prelude (Integer, String)
import qualified Prelude as C
  ( Eq, Ord, Show, Read
  , Functor, Foldable, Traversable
  , Int, Maybe(..)
  )
import qualified Data.String

type Program = Program' BNFC'Position
data Program' a = ProgramT a [TopDef' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type TopDef = TopDef' BNFC'Position
data TopDef' a
    = FnDef a (Type' a) Ident [Arg' a] (Block' a)
    | ClDef a Ident (ClBlock' a)
    | SubClDef a Ident Ident (ClBlock' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Arg = Arg' BNFC'Position
data Arg' a = ArgT a (Type' a) Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type ClBlock = ClBlock' BNFC'Position
data ClBlock' a = ClBlockT a [InClDef' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type InClDef = InClDef' BNFC'Position
data InClDef' a
    = MthDef a (Type' a) Ident [Arg' a] (Block' a)
    | FldDef a (Type' a) Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Block = Block' BNFC'Position
data Block' a = BlockT a [Stmt' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Stmt = Stmt' BNFC'Position
data Stmt' a
    = Empty a
    | BStmt a (Block' a)
    | Decl a (Type' a) [Item' a]
    | Ass a (Expr' a) (Expr' a)
    | Incr a Ident
    | Decr a Ident
    | Ret a (Expr' a)
    | VRet a
    | Cond a (Expr' a) (Stmt' a)
    | CondElse a (Expr' a) (Stmt' a) (Stmt' a)
    | While a (Expr' a) (Stmt' a)
    | For a (Type' a) Ident (Expr' a) (Stmt' a)
    | SExp a (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Item = Item' BNFC'Position
data Item' a = NoInit a Ident | Init a Ident (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Type = Type' BNFC'Position
data Type' a
    = Int a | Bool a | Void a | Str a | Arr a (Type' a) | Cl a Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Expr = Expr' BNFC'Position
data Expr' a
    = EVar a Ident
    | ELitInt a Integer
    | EString a String
    | ELitTrue a
    | ELitFalse a
    | ECastId a (Expr' a)
    | ECastArr a (Type' a)
    | ECast a (Type' a)
    | EFun a Ident [Expr' a]
    | EMth a (Expr' a) Ident [Expr' a]
    | EInd a (Expr' a) (Expr' a)
    | EAcc a (Expr' a) Ident
    | ENew a (Type' a)
    | ENewArr a (Type' a) (Expr' a)
    | ENeg a (Expr' a)
    | ENot a (Expr' a)
    | EMul a (Expr' a) (MulOp' a) (Expr' a)
    | EAdd a (Expr' a) (AddOp' a) (Expr' a)
    | ERel a (Expr' a) (RelOp' a) (Expr' a)
    | EAnd a (Expr' a) (Expr' a)
    | EOr a (Expr' a) (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type AddOp = AddOp' BNFC'Position
data AddOp' a = Plus a | Minus a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type MulOp = MulOp' BNFC'Position
data MulOp' a = Times a | Div a | Mod a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type RelOp = RelOp' BNFC'Position
data RelOp' a = LTH a | LE a | GTH a | GE a | EQU a | NE a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

newtype Ident = Ident String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

-- | Start position (line, column) of something.

type BNFC'Position = C.Maybe (C.Int, C.Int)

pattern BNFC'NoPosition :: BNFC'Position
pattern BNFC'NoPosition = C.Nothing

pattern BNFC'Position :: C.Int -> C.Int -> BNFC'Position
pattern BNFC'Position line col = C.Just (line, col)

-- | Get the start position of something.

class HasPosition a where
  hasPosition :: a -> BNFC'Position

instance HasPosition Program where
  hasPosition = \case
    ProgramT p _ -> p

instance HasPosition TopDef where
  hasPosition = \case
    FnDef p _ _ _ _ -> p
    ClDef p _ _ -> p
    SubClDef p _ _ _ -> p

instance HasPosition Arg where
  hasPosition = \case
    ArgT p _ _ -> p

instance HasPosition ClBlock where
  hasPosition = \case
    ClBlockT p _ -> p

instance HasPosition InClDef where
  hasPosition = \case
    MthDef p _ _ _ _ -> p
    FldDef p _ _ -> p

instance HasPosition Block where
  hasPosition = \case
    BlockT p _ -> p

instance HasPosition Stmt where
  hasPosition = \case
    Empty p -> p
    BStmt p _ -> p
    Decl p _ _ -> p
    Ass p _ _ -> p
    Incr p _ -> p
    Decr p _ -> p
    Ret p _ -> p
    VRet p -> p
    Cond p _ _ -> p
    CondElse p _ _ _ -> p
    While p _ _ -> p
    For p _ _ _ _ -> p
    SExp p _ -> p

instance HasPosition Item where
  hasPosition = \case
    NoInit p _ -> p
    Init p _ _ -> p

instance HasPosition Type where
  hasPosition = \case
    Int p -> p
    Bool p -> p
    Void p -> p
    Str p -> p
    Arr p _ -> p
    Cl p _ -> p

instance HasPosition Expr where
  hasPosition = \case
    EVar p _ -> p
    ELitInt p _ -> p
    EString p _ -> p
    ELitTrue p -> p
    ELitFalse p -> p
    ECastId p _ -> p
    ECastArr p _ -> p
    ECast p _ -> p
    EFun p _ _ -> p
    EMth p _ _ _ -> p
    EInd p _ _ -> p
    EAcc p _ _ -> p
    ENew p _ -> p
    ENewArr p _ _ -> p
    ENeg p _ -> p
    ENot p _ -> p
    EMul p _ _ _ -> p
    EAdd p _ _ _ -> p
    ERel p _ _ _ -> p
    EAnd p _ _ -> p
    EOr p _ _ -> p

instance HasPosition AddOp where
  hasPosition = \case
    Plus p -> p
    Minus p -> p

instance HasPosition MulOp where
  hasPosition = \case
    Times p -> p
    Div p -> p
    Mod p -> p

instance HasPosition RelOp where
  hasPosition = \case
    LTH p -> p
    LE p -> p
    GTH p -> p
    GE p -> p
    EQU p -> p
    NE p -> p

