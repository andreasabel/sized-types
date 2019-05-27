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


-- Inverses: A relation between two morphisms (symmetric perspective).
------------------------------------------------------------------------

module _ {A B : Obj} where

  module _ (f : Hom A B) (g : Hom B A) where

    Inverses : Set _
    Inverses = (g ∘ f) ≈ id _

module _ {A : Obj} where

  idInverses : Inverses (id A) (id A)
  idInverses = comp-id-l

module _ {A B C : Obj}
  {f : Hom A B} {f⁻¹ : Hom B A} (fI : Inverses f f⁻¹)
  {g : Hom B C} {g⁻¹ : Hom C B} (gI : Inverses g g⁻¹)
  where

  compInverses : Inverses (g ∘ f) (f⁻¹ ∘ g⁻¹)
  compInverses = begin
    (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) ≈⟨ comp-assoc ⟩
    f⁻¹ ∘ (g⁻¹ ∘ (g ∘ f)) ≈⟨ comp-congʳ (symEq comp-assoc) ⟩
    f⁻¹ ∘ ((g⁻¹ ∘ g) ∘ f) ≈⟨ comp-congʳ (comp-congˡ gI) ⟩
    f⁻¹ ∘ (id B ∘ f)      ≈⟨ comp-congʳ comp-id-l ⟩
    f⁻¹ ∘ f               ≈⟨ fI ⟩
    id A ∎

-- Inverses to a given morphism f.
------------------------------------------------------------------------

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

-- Isomorphism between objects.
------------------------------------------------------------------------

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

module _ where

  module _ {A B C : Obj} {f : Hom A B} {g : Hom B C}  where

    module _ (fLI : LeftInverse f) (open LeftInverse fLI using () renaming (leftInverse to f⁻¹))
             (gLI : LeftInverse g) (open LeftInverse gLI using () renaming (leftInverse to g⁻¹))
             (open LeftInverse) where

      compLeftInverse : LeftInverse (g ∘ f)
      compLeftInverse .leftInverse   = f⁻¹ ∘ g⁻¹
      compLeftInverse .isLeftInverse = compInverses (fLI .isLeftInverse) (gLI .isLeftInverse)

    module _ (fRI : RightInverse f) (open RightInverse fRI using () renaming (rightInverse to f⁻¹))
             (gRI : RightInverse g) (open RightInverse gRI using () renaming (rightInverse to g⁻¹))
             (open RightInverse) where

      compRightInverse : RightInverse (g ∘ f)
      compRightInverse .rightInverse   = f⁻¹ ∘ g⁻¹
      compRightInverse .isRightInverse = compInverses (gRI .isRightInverse) (fRI .isRightInverse)

    module _ (fI : Inverse f) (open Inverse fI using () renaming (inverse to f⁻¹))
             (gI : Inverse g) (open Inverse gI using () renaming (inverse to g⁻¹))
             (open Inverse) (open IsInverse) where

      compInverse : Inverse (g ∘ f)
      compInverse .inverse   = f⁻¹ ∘ g⁻¹
      compInverse .isInverse .isLeftInverse  = compInverses (fI .isLeftInverse)  (gI .isLeftInverse)
      compInverse .isInverse .isRightInverse = compInverses (gI .isRightInverse) (fI .isRightInverse)

  module _ {A B C : Obj} (f : Hom A B) (g : Hom B C) where
