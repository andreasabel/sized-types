{-# OPTIONS --postfix-projections #-}

-- Invertible arrows

open import Library
open import Category

module Isomorphism {o h e} {C : Category o h e} where

open Category.Category C renaming
  ( comp to _∘_
  ; Eq   to _≈_
  )
open EqReasoning

module _ {A B : Obj} (f : Hom A B) where

  IsLeftInverse : (g : Hom B A) → Set _
  IsLeftInverse g = (g ∘ f) ≈ id _

  record LeftInverse : Set (h ⊔ e) where
    field
      leftInverse : Hom B A
      isLeftInverse : IsLeftInverse leftInverse

  IsRightInverse : (g : Hom B A) → Set _
  IsRightInverse g = (f ∘ g) ≈ id _

  record RightInverse : Set (h ⊔ e) where
    field
      rightInverse : Hom B A
      isRightInverse : IsRightInverse rightInverse

  record IsInverse (g : Hom B A) : Set e where
    field
      isLeftInverse  : IsLeftInverse g
      isRightInverse : IsRightInverse g

  record Inverse : Set (h ⊔ e) where
    field
      inverse : Hom B A
      isInverse : IsInverse inverse
    open IsInverse isInverse public

module _ (A B : Obj) where

  record Isomorphic : Set (h ⊔ e) where
    field
      morphism : Hom A B
      hasInverse : Inverse morphism
    open Inverse hasInverse public

record Isomorphism : Set (o ⊔ h ⊔ e) where
  field
    {src tgt} : Obj
    isomorphic : Isomorphic src tgt
  open Isomorphic isomorphic public

module _ (open Inverse) (open Isomorphic) (open Isomorphism) where

  -- The inverse to id is id itself.

  module _ {A : Obj} (open IsInverse) where

    idIsInverse : IsInverse (id A) (id A)
    idIsInverse .isLeftInverse  = comp-id-l
    idIsInverse .isRightInverse = comp-id-l

    idInverse :  Inverse (id A)
    idInverse .inverse   = id A
    idInverse .isInverse = idIsInverse

    idIsomorphic : Isomorphic A A
    idIsomorphic .morphism   = id A
    idIsomorphic .hasInverse = idInverse

  -- Every object is ismorphic to itself via id.

  module _ (A : Obj) where

    idIsomorphism : Isomorphism
    idIsomorphism .src = A
    idIsomorphism .tgt = A
    idIsomorphism .isomorphic = idIsomorphic

  -- On inverses of a composition

  module _ {A B C : Obj} {f : Hom A B} {g : Hom B C}  where

    module _ (fLI : LeftInverse f) (open LeftInverse fLI using () renaming (leftInverse to f⁻¹))
             (gLI : LeftInverse g) (open LeftInverse gLI using () renaming (leftInverse to g⁻¹))
             (open LeftInverse) where

      compLeftInverse : LeftInverse (g ∘ f)
      compLeftInverse .leftInverse   = f⁻¹ ∘ g⁻¹
      compLeftInverse .isLeftInverse = begin
        (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) ≈⟨ comp-assoc ⟩
        f⁻¹ ∘ (g⁻¹ ∘ (g ∘ f)) ≈⟨ comp-congʳ (symEq comp-assoc) ⟩
        f⁻¹ ∘ ((g⁻¹ ∘ g) ∘ f) ≈⟨ comp-congʳ (comp-congˡ (gLI .isLeftInverse)) ⟩
        f⁻¹ ∘ (id B ∘ f)      ≈⟨ comp-congʳ comp-id-l ⟩
        f⁻¹ ∘ f               ≈⟨ fLI .isLeftInverse ⟩
        id A ∎

    module _ (fLI : RightInverse f) (open RightInverse fLI using () renaming (rightInverse to f⁻¹))
             (gLI : RightInverse g) (open RightInverse gLI using () renaming (rightInverse to g⁻¹))
             (open RightInverse) where

      compRightInverse : RightInverse (g ∘ f)
      compRightInverse .rightInverse   = f⁻¹ ∘ g⁻¹
      compRightInverse .isRightInverse = begin
        (g ∘ f) ∘ (f⁻¹ ∘ g⁻¹) ≈⟨ comp-assoc ⟩
        g ∘ (f ∘ (f⁻¹ ∘ g⁻¹)) ≈⟨ comp-congʳ (symEq comp-assoc) ⟩
        g ∘ ((f ∘ f⁻¹) ∘ g⁻¹) ≈⟨ comp-congʳ (comp-congˡ (fLI .isRightInverse)) ⟩
        g ∘ (id B ∘ g⁻¹)      ≈⟨ comp-congʳ comp-id-l ⟩
        g ∘ g⁻¹               ≈⟨ gLI .isRightInverse ⟩
        id C ∎

  module _ {A B C : Obj} (f : Hom A B) (g : Hom B C) where
