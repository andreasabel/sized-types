{-# OPTIONS --postfix-projections #-}

open import Library
open import Category
open import Category.Finality
import Isomorphism

module Category.Initiality where

-- Initiality and initial objects

module Initiality {o h e} (C : Category o h e) where
  open Finality (op C) public using () renaming
    ( Terminal           to Initial
    ; !                  to ¿
    ; !-unique           to ¿-unique
    ; 𝟙                  to 𝟘
    ; terminal           to initial
    ; TerminalObject     to InitialObject
    ; WeakTerminalObject to WeakInitialObject
    )

module InitialityALT {o h e} (C : Category o h e) where
  open Category.Category
  open Finality

  Initial : (X : C .Obj) → Set (o ⊔ h ⊔ e)
  Initial = Terminal (op C)

  module Initial X (init : Initial X) = Terminal {C = op C} init
    renaming (! to ¿; !-unique to ¿-unique)

  record InitialObject : Set (o ⊔ h ⊔ e) where
    field
      𝟘       : C .Obj
      initial : Initial 𝟘


-- The initial object is unique up to isomorphism.
------------------------------------------------------------------------

module _ {o h e} {C : Category o h e} where

  -- open Category.Category C renaming (comp to _∘_; Eq to _≈_)
  open Initiality C
  open Finality (op C)
  open Isomorphism {C = op C}

  initial-unique : ∀{𝟘 𝟘'} (i : Initial 𝟘) (i' : Initial 𝟘') → Isomorphic 𝟘 𝟘'
  initial-unique i i' = terminal-unique i i'

-- -}
