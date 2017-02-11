{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- | Substitution and weak head evaluation

module Evaluation where

import Internal

import Impossible
#include "undefined.h"

-- | Substitutions are lists of terms.

type Subst = [Term]

-- | Weakening substitution @Γ.Δ ⊢ wkS |Δ| : Γ@

wkS :: Int -> Subst
wkS n = map (var . Index) [n,n+1..]

-- | Identity substitution @Γ ⊢ idS : Γ@.

idS :: Subst
idS = wkS 0

-- | Composing substitution
--   @
--      Γ₁ ⊢ τ : Γ₂    Γ₂ ⊢ σ : Γ₃
--      -------------------------
--      Γ₁ ⊢ compS τ σ : Γ₃
--   @

compS :: Subst -> Subst -> Subst
compS = subst

-- | Extending a substitution
--   @
--      Γ ⊢ σ : Δ    Δ ⊢ T    Γ ⊢ t : Tσ
--      --------------------------------
--      Γ ⊢ consS t σ : Δ.T
--   @

consS :: Term -> Subst -> Subst
consS = (:)

-- | Lifting a substitution under a binder.
--   @
--      Γ ⊢ σ : Δ      Δ ⊢ T
--      --------------------
--      Γ.Tσ ⊢ liftS σ : Δ.T
--   @

liftS :: Subst -> Subst
liftS s = consS (var 0) $ weakS s

-- | Weakening a substitution.
--
--   @
--     Γ ⊢ σ : Δ    Γ ⊢ T
--     ------------------
--     Γ.T ⊢ weakS σ : Δ
--   @

weakS :: Subst -> Subst
weakS = compS (wkS 1)

-- | Looking up an entry in a substitution.

lookupS :: Subst -> Index -> Term
lookupS s i =  s !! dbIndex i

-- | Substitution for various syntactic categories.

class Substitute a where
  subst      :: Subst -> a -> a
  subst s t = substApply t s []

  applyE     :: a -> Elims -> a
  applyE t [] = t
  applyE t es = substApply t idS es

  substApply :: a -> Subst -> Elims -> a
  substApply t s es = subst s t `applyE` es

instance Substitute a => Substitute [a] where
  subst s            = map (subst s)
  applyE ts es       = map (`applyE` es) ts
  substApply ts s es = map (\ t -> substApply t s es) ts

instance Substitute a => Substitute (Dom a) where
  subst s            = fmap (subst s)
  applyE ts es       = fmap (`applyE` es) ts
  substApply ts s es = fmap (\ t -> substApply t s es) ts

instance Substitute a => Substitute (Arg a) where
  subst s            = fmap (subst s)
  applyE ts es       = fmap (`applyE` es) ts
  substApply ts s es = fmap (\ t -> substApply t s es) ts

instance Substitute a => Substitute (Elim' a) where
  subst s            = fmap (subst s)
  applyE ts es       = fmap (`applyE` es) ts
  substApply ts s es = fmap (\ t -> substApply t s es) ts

instance Substitute Term where
  substApply t s es = case t of
    Type l
      | null es   -> Type $ subst s l
      | otherwise -> __IMPOSSIBLE__
    Size
      | null es   -> Size
      | otherwise -> __IMPOSSIBLE__
    Nat a
      | null es   -> Nat $ subst s a
      | otherwise -> __IMPOSSIBLE__
    Zero
      | null es   -> Zero
      | otherwise -> __IMPOSSIBLE__
    Suc t
      | null es   -> Suc $ subst s t
      | otherwise -> __IMPOSSIBLE__
    Infty
      | null es   -> Infty
      | otherwise -> __IMPOSSIBLE__
    Pi u t
      | null es   -> Pi (subst s u) $ subst s t
      | otherwise -> __IMPOSSIBLE__
    Var i es -> lookupS s i `applyE` subst s es

instance Substitute (Abs Term) where
