{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

-- | Internal Syntax.

module Internal where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Sit.Abs (Ident)

-- | Variables are de Bruijn indices.

newtype Index = Index { dbIndex :: Int }
  deriving (Eq, Ord, Show, Enum, Num)

-- | Size expressions.

data Size' a
  = SVar a Integer
    -- ^ @i + k@: Size variable plus offset.
  | SConst Integer
    -- ^ @k@:     Constant finite size.
  | SInfty
    -- ^ @oo@:    Infinity size.
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type Size = Size' Index
type Level = Size

-- | Terms/types

type Type = Term

data Term
  = -- | Universe with level.
    Type Level
  | -- | Type of sizes (internal use only).
    Size
  | -- | Sized natural number type.
    Nat Size
  | -- | Zero constructor.
    Zero
  | -- | Successor constructor.
    Suc Term
  | -- ^ (Dependent) function type.
    Pi (Dom Type) (Abs Term)
  | -- ^ Lambda abstraction
    Lam ArgInfo (Abs Term)
  | -- ^ Application (neutral).
    Var Index Elims
  | -- ^ Function call
    Def Ident Elims
  deriving (Eq, Ord, Show)

-- | Eliminations.

type Elims = [ Elim ]
type Elim  = Elim' Term

data Elim' a
  = -- | Function application.
    Apply (Arg Term)
  | -- | Case distinction
    Case
    { caseReturn :: a -- ^ @T : Nat (b + 1) -> Setω@
    , caseZero   :: a -- ^ @tz : T zero@
    , caseSuc    :: a -- ^ @ts : (t : Nat b) -> T (suc t)@
    }
  | -- | Recursion
    Fix
    { fixReturn :: a
      -- ^ @T : ..(i : Size) -> Nat i -> Setω@
    , fixBody   :: a
      -- ^ @t : .(i : Size) (f : (x : Nat i) -> T i x) (x : Nat (i + 1)) -> T (i + 1) x@
    }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | Abstraction.

type AbsName = String

data Abs a
  = -- | Actual abstraction (body contains one more index).
    Abs   { absName :: AbsName, absBody :: a }
  | -- | No abstraction (argument will be ignored).
    NoAbs { absName :: AbsName, absBody :: a }
  deriving (Eq, Ord, Show)

-- | Function domain decoration.

data Dom a = Dom { domInfo :: ArgInfo, unDom :: a }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | Argument decoration.

data Arg a = Arg { argInfo :: ArgInfo, unArg :: a }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type ArgInfo = Relevance

-- | Relevance lattice (order matters)
data Relevance
  = Relevant
  | ShapeIrr
  | Irrelevant
  deriving (Eq, Ord, Show)
