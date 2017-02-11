{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}

-- | Values and weak head evaluation

module Evaluation where

import Control.Applicative
import Control.Monad

import Sit.Abs (Ident)
import Internal

import Impossible
#include "undefined.h"

-- | Generic values are de Bruijn levels.
type VGen   = Int

type VSize  = Size' VGen
type VLevel = VSize

type VType  = Val
type VElim  = Elim' VGen
type VElims = [VElim]

data Val
  = VType VLevel
  | VSize
  | VNat VSize
  | VZero
  | VSuc Val
  | VPi (Dom VType) VClos
  | VLam VClos
  | -- | Neutrals.
    VUp VType VNe
  | -- | Type annotation for readback
    VDown VType Val

data VNe
  = VNe VLevel VElims

data VClos = VClos
  { closBody :: Abs Term
  , closEnv  :: Env
  }

-- | An environment maps de Bruijn indices to values.
--   The first entry in the list is the binding for index 0.

type Env = [Val]

-- | Evaluation monad.

class (Functor m, Applicative m, Monad m) => MonadEval m where
  getDef :: Ident -> m Val

-- | Evaluation.

class Evaluate a b where
  eval :: MonadEval m => a -> Env -> m b

instance Evaluate Size VSize where
  eval a rho = case a of
    SVar i k ->  __IMPOSSIBLE__

instance Evaluate Term Val where
  eval t rho = case t of
    _ -> __IMPOSSIBLE__
