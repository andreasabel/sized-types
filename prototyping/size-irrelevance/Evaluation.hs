{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
-- {-# LANGUAGE FunctionalDependencies, UndecidableInstances #-}

-- | Values and weak head evaluation

module Evaluation where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader

import Data.Traversable (traverse)

import Sit.Abs (Ident)
import Internal

import Impossible
#include "undefined.h"

-- | Generic values are de Bruijn levels.
type VGen   = Int

type VSize  = Val
type VLevel = VSize

type VType  = Val
type VElim  = Elim' Val
type VElims = [VElim]

data Val
  = VType VLevel
  | VSize
  | VNat VSize
  | VZero
  | VSuc Val
  | VInfty
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

evaluate :: MonadEval m => Term -> Env -> m Val
evaluate t rho = runReaderT (eval t) rho

class Evaluate a b where -- -- | a -> b where
  eval :: MonadEval m => a -> ReaderT Env m b

instance Evaluate Index Val where
  eval (Index i) = (!! i) <$> ask

instance Evaluate Term Val where
  eval t = case t of
    Type l   -> VType <$> eval l
    Nat a    -> VNat <$> eval a
    Size     -> pure VSize
    Infty    -> pure VInfty
    Zero     -> pure VZero
    Suc t    -> VSuc <$> eval t
    Pi u t   -> liftA2 VPi (eval u) (eval t)
    Lam ai t -> VLam <$> eval t
    Var x es -> do
      h   <- eval x
      ves <- mapM eval es
      lift $ apply h ves
    Def f es -> do
      h   <- lift $ getDef f
      ves <- mapM eval es
      lift $ apply h ves

instance Evaluate (Abs Term) VClos where
  eval t = VClos t <$> ask

instance Evaluate a b => Evaluate [a] [b] where
  eval = traverse eval

instance Evaluate a b => Evaluate (Dom a) (Dom b) where
  eval = traverse eval

instance Evaluate a b => Evaluate (Elim' a) (Elim' b) where
  eval = traverse eval

apply :: MonadEval m => Val -> VElims -> m Val
apply v []       = return v
apply v (e : es) = (`apply` es) =<<
  case (v, e) of
    (VLam cl , Apply u   ) -> applyClos cl $ unArg u
    (VZero   , Case _ u _) -> return u
    (VSuc n  , Case _ _ f) -> apply f [ Apply $ defaultArg n ]
    (VZero   , Fix _ f   ) -> apply f $ map (Apply . defaultArg) [ v , VZero ]
-- apply1 :: MonadEval m => Val -> Val -> m Val
-- apply1

applyClos :: MonadEval m => VClos -> Val -> m Val
applyClos (VClos b rho) u = case b of
  NoAbs _ t -> evaluate t rho
  Abs   _ t -> evaluate t (u : rho)
