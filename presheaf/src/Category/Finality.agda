{-# OPTIONS --postfix-projections #-}

open import Library
open import Category
import Isomorphism

module Category.Finality where

-- Finality and terminal objects
------------------------------------------------------------------------

module Finality {o h e} (C : Category o h e) where

  open Category.Category C renaming (Eq to _≈_)

  WeaklyTerminal : (𝟙 : Obj) → Set (o ⊔ h)
  WeaklyTerminal 𝟙 = (A : Obj) → Hom A 𝟙

  record WeakTerminalObject : Set (o ⊔ h ⊔ e) where
    field
      𝟙 : Obj
      ! : (A : Obj) → Hom A 𝟙

  record Terminal (𝟙 : Obj) : Set (o ⊔ h ⊔ e) where
    field
      !        : WeaklyTerminal 𝟙
      !-unique : ∀{A} (f : Hom A 𝟙) → f ≈ ! A

  record TerminalObject : Set (o ⊔ h ⊔ e) where
    field
      𝟙        : Obj
      terminal : Terminal 𝟙

  open Terminal           public
  open TerminalObject     public
  open WeakTerminalObject public

module _ {o h e} {C : Category o h e} (open Finality C) where

  weakTerminalObject : TerminalObject → WeakTerminalObject
  weakTerminalObject t .𝟙 = t .𝟙
  weakTerminalObject t .! = t .terminal .!

-- The terminal object is unique up to isomorphism.
------------------------------------------------------------------------

module _ {o h e} {C : Category o h e} where

  open Category.Category C renaming (comp to _∘_; Eq to _≈_)
  open EqReasoning
  open Isomorphism {C = C}

  module _ (open Finality C) where

    terminal-unique : ∀{𝟙 𝟙' : Obj} (t : Terminal 𝟙) (t' : Terminal 𝟙') → Isomorphic 𝟙 𝟙'
    terminal-unique record { ! = ! ; !-unique = !-unique } record { ! = !' ; !-unique = !'-unique } .Isomorphic.morphism = !' _
    terminal-unique record { ! = ! ; !-unique = !-unique } record { ! = !' ; !-unique = !'-unique } .Isomorphic.hasInverse .Inverse.inverse = ! _
    terminal-unique record { ! = ! ; !-unique = !-unique } record { ! = !' ; !-unique = !'-unique } .Isomorphic.hasInverse .Inverse.isInverse .IsInverse.isLeftInverse = begin
      ! _ ∘ !' _  ≈⟨ !-unique _ ⟩
      ! _         ≈⟨ symEq (!-unique _) ⟩
      id _ ∎
    terminal-unique record { ! = ! ; !-unique = !-unique } record { ! = !' ; !-unique = !'-unique } .Isomorphic.hasInverse .Inverse.isInverse .IsInverse.isRightInverse = begin
      !' _ ∘ ! _  ≈⟨ !'-unique _ ⟩
      !' _        ≈⟨ symEq (!'-unique _) ⟩
      id _ ∎
