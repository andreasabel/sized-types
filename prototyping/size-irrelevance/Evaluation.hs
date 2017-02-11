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
  | VZero VSize
  | VSuc VSize Val
  | VInfty
  | VPi (Dom VType) VClos
  | VLam VClos
  | -- | @\ x -> x e@ for internal use in fix.
    VElimBy VElim
  | -- | Neutrals.
    VUp VType VNe
  | -- | Type annotation for readback (normal form).
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
  eval = \case
    Type l   -> VType <$> eval l
    Nat a    -> VNat <$> eval a
    Size     -> pure VSize
    Infty    -> pure VInfty
    Zero a   -> VZero <$> eval a
    Suc a t  -> liftA2 VSuc (eval a) (eval t)
    Pi u t   -> liftA2 VPi (eval u) (eval t)
    Lam ai t -> VLam <$> eval t
    Var x es -> do
      h   <- eval x
      ves <- mapM eval es
      lift $ applyE h ves
    Def f es -> do
      h   <- lift $ getDef f
      ves <- mapM eval es
      lift $ applyE h ves

instance Evaluate (Abs Term) VClos where
  eval t = VClos t <$> ask

instance Evaluate a b => Evaluate [a] [b] where
  eval = traverse eval

instance Evaluate a b => Evaluate (Dom a) (Dom b) where
  eval = traverse eval

instance Evaluate a b => Evaluate (Elim' a) (Elim' b) where
  eval = traverse eval

applyE :: MonadEval m => Val -> VElims -> m Val
applyE v []       = return v
applyE v (e : es) = (`applyE` es) =<<
  case (v, e) of
    (_        , Apply u   ) -> apply v u
    (VZero _  , Case _ u _) -> return u
    (VSuc _ n , Case _ _ f) -> apply f $ defaultArg n
    (VZero a  , Fix t f   ) -> unfoldFix t f a v -- apply f $ e : map (Apply . defaultArg) [ v , VZero ]
    (VSuc a n , Fix t f   ) -> unfoldFix t f a v
    (VUp (VNat a) n , _)    -> elimNeNat a n e
    _ -> __IMPOSSIBLE__

-- | Apply a function to an argument.

apply :: MonadEval m => Val -> Arg Val -> m Val
apply v arg@(Arg ai u) = case v of
  VLam cl   -> applyClos cl u
  VElimBy e -> applyE u [ e ]
  VUp (VPi a b) (VNe x es) -> do
    t' <- applyClos b u
    return $ VUp t' $ VNe x $ es ++ [ Apply $ Arg ai $ VDown (unDom a) u ]

-- | Apply a closure to a value.

applyClos :: MonadEval m => VClos -> Val -> m Val
applyClos (VClos b rho) u = case b of
  NoAbs _ t -> evaluate t rho
  Abs   _ t -> evaluate t $ u : rho

-- | Unfold a fixed-point.

unfoldFix :: MonadEval m => VType -> Val -> VSize -> Val -> m Val
unfoldFix t f a v = applyE f $ map (Apply . defaultArg) [ a , VElimBy (Fix t f) , v ]

-- | Eliminate a neutral natural number.

elimNeNat :: MonadEval m => VSize -> VNe -> VElim -> m Val
elimNeNat a n e = __IMPOSSIBLE__

-- | Readback.

class Readback a b where
  readback :: MonadEval m => a -> ReaderT Int m b

instance Readback VGen Index where
  readback k = Index (- 1 - n) <$> ask

instance Readback Val Term where
  readback = \case
    VDown (VType _) d -> readbackType d
    VDown (VNat _ ) d -> readbackNat  d

    VDown (VPi a b) d -> do
      v0 <- VUp (unDom a) . (`VNe` []) <$> ask
      c <- applyClos b v0
      Lam (domInfo a) <$> do
        local succ . readback . VDown c =<< do
          apply d $ Arg (domInfo a) v0

    VDown (VUp _  ) (VUp _ n) -> readbackNe n

readbackType :: MonadEval m => Val -> ReaderT Int m Term
readbackType = \case
  VSize   -> pure Size
  VType a -> Type <$> readbackSize a
  VNat a  -> Nat  <$> readbackSize a
  VPi a b -> do
    u  <- traverse readbackType u
    v0 <- VUp (unDom a) . (`VNe` []) <$> ask
    readbackType =<< applyClos b v0
  VUp _ n -> readbackNe n
  _ -> __IMPOSSIBLE__

readbackNat  :: MonadEval m => Val -> ReaderT Int m Term
readbackNat = \case
  VZero a        -> Zero $ readbackSize a
  VSuc a t       -> liftA2 Suc (readbackSize a) (readbackNat t)
  VUp (VNat _) n -> readbackNe n
  _ -> __IMPOSSIBLE__

readbackNe  :: MonadEval m => VNe -> ReaderT Int m Term
readbackNe = \case
  _ -> __IMPOSSIBLE__

readbackSize  :: MonadEval m => Val -> ReaderT Int m Term
readbackSize = \case
  VInfty   -> pure Infty
  VZero _  -> pure sZero
  VSuc _ a -> sSuc <$> readBackSize a
  VUp VSize (VNe x []) -> Var <$> readback x
  _ -> __IMPOSSIBLE__
