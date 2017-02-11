{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Internal Syntax.

module Internal where

-- | Variables are de Bruijn indices.

newtype Index = Index { dbIndex :: Int }
  deriving (Eq, Ord, Show, Enum, Num)

-- | Size expressions.

data Size
  = SVar Index Integer
    -- ^ @i + k@: Size variable plus offset.
  | SConst Integer
    -- ^ @k@:     Constant finite size.
  | SInfty
    -- ^ @oo@:    Infinity size.
  deriving (Eq, Ord, Show)

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
  deriving (Eq, Ord, Show)

-- | Eliminations.

type Elims = [ Elim ]

data Elim
  = -- | Function application.
    Apply (Arg Term)
  | -- | Case distinction
    Case
    { caseReturn :: Type -- ^ @T : Nat (b + 1) -> Setω@
    , caseZero   :: Term -- ^ @tz : T zero@
    , caseSuc    :: Term -- ^ @ts : (t : Nat b) -> T (suc t)@
    }
  | -- | Recursion
    Fix
    { fixReturn :: Term
      -- ^ @T : ..(i : Size) -> Nat i -> Setω@
    , fixBody   :: Term
      -- ^ @t : .(i : Size) (f : (x : Nat i) -> T i x) (x : Nat (i + 1)) -> T (i + 1) x@
    }
  deriving (Eq, Ord, Show)

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
  deriving (Eq, Ord, Show)

-- | Argument decoration.

data Arg a = Arg { argInfo :: ArgInfo, unArg :: a }
  deriving (Eq, Ord, Show)

type ArgInfo = Relevance

-- | Relevance lattice (order matters)
data Relevance
  = Relevant
  | ShapeIrr
  | Irrelevant
  deriving (Eq, Ord, Show)
