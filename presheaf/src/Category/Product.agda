{-# OPTIONS --postfix-projections #-}

open import Library
open import Category
open import Category.Discrete
open import Category.Finality
open import Category.Limits

module Category.Product {o h e} {C : Category o h e} where

-- Given two objects A and B, a span A ⇐ C ⇒ B arises
-- as a cone of the functor
--
--   true  ↦ A
--   false ↦ B
--
-- The product of A and B is the terminal cone/span.

open Category.Category C renaming (Eq to _≈_; comp to _∘_)
open Functor

-- Notions of products of two objects.

module ProductNotion (A B : Obj) where

  -- The diagram for the limit is simply the two objects A and B (no morphism).

  -- diagram : DiscreteFunctor Bool C
  diagram = discreteFunctor Bool C λ where
    false → A
    true  → B

  module Limit = Limits diagram

  open Limit public using () renaming
    ( Cone        to Span
    ; Limit       to Product
    ; IsLimit     to IsProduct
    ; WeakLimit   to WeakProduct
    ; IsWeakLimit to IsWeakProduct
    )

hasProducts : Set _
hasProducts = (A B : Obj) → ProductNotion.Product A B

-- Fix two objects A and B.

module _ {A B : Obj} (open ProductNotion A B) where

  open Limits using (Cone; module ConeHom)
  open Finality
  open EqReasoning

  module WeakProductAPI (P : WeakProduct) where

    open Cone      (P .𝟙)    public using () renaming (Src to A×B; cone to π)
    module _ (sp : Span) where
      open ConeHom (P .! sp) public using () renaming (coneHom to pair)
    module _ {sp : Span} where
      open ConeHom (P .! sp) public using () renaming (tri to β)

    -- Common notation for the projections.

    π₁ = π false
    π₂ = π true

    -- Common notation for the pairing.

    module _ {C : Obj} (f : Hom C A) (g : Hom C B) where

      span : Span
      span .Cone.Src = _
      span .Cone.cone false = f
      span .Cone.cone true  = g
      span .Cone.coh  refl  = comp-id-l

      ⟨_,_⟩ :  Hom C A×B
      ⟨_,_⟩ = pair span

{-
    -- Weak product should imply the congruence property, but does not seem to,
    -- since objects do not have a setoid structure.

    module _ {C} {f f' : Hom C A} {g g' : Hom C B} (ef : f ≈ f') (eg : g ≈ g') where
      open Category.Category using (Eq)

      span-cong : {!!} .Eq (span f g) (span f' g')
      span-cong = {!!}

      pair-cong : ⟨ f , g ⟩ ≈ ⟨ f' , g' ⟩
      pair-cong = {!!}
-}

    -- Notation for the β-laws.

    module _ {C : Obj} {f : Hom C A} {g : Hom C B} where

      β₁ : π₁ ∘ ⟨ f , g ⟩ ≈ f
      β₁ = β false

      β₂ : π₂ ∘ ⟨ f , g ⟩ ≈ g
      β₂ = β true

    -- Universality of pairing

    PairExtensionality = ∀ {C : Obj} {f : Hom C A} {g : Hom C B} {h : Hom C A×B}
      → π₁ ∘ h ≈ f
      → π₂ ∘ h ≈ g
      →      h ≈ ⟨ f , g ⟩

    -- Further extensionality principles

    Eta = id A×B ≈ ⟨ π₁ , π₂ ⟩

    Extensionality = ∀ {C : Obj} {h h' : Hom C A×B}
      → π₁ ∘ h ≈ π₁ ∘ h'
      → π₂ ∘ h ≈ π₂ ∘ h'
      →      h ≈ h'

    -- Permutation principle

    PairComp = ∀ {C D} {f : Hom C A} {g : Hom C B} {h : Hom D C} →
      ⟨ f , g ⟩ ∘ h ≈ ⟨ f ∘ h , g ∘ h ⟩

    -- Congruence

    PairCong = ∀ {C} {f f' : Hom C A} {g g' : Hom C B}
      → (ef : f ≈ f')
      → (eg : g ≈ g')
      → ⟨ f , g ⟩ ≈ ⟨ f' , g' ⟩

    -- Univerality implies the other principles

    module UniversalityConsequences (pair-extensionality : PairExtensionality) where

      η : Eta
      η = pair-extensionality comp-id-r comp-id-r

      pair-comp : PairComp
      pair-comp {f = f} {g = g} {h = h} = pair-extensionality
          (begin
            π₁ ∘ (⟨ f , g ⟩ ∘ h)  ≈⟨ symEq comp-assoc ⟩
            (π₁ ∘ ⟨ f , g ⟩) ∘ h  ≈⟨ comp-congˡ β₁    ⟩
            f ∘ h                 ∎)
          (begin
            π₂ ∘ (⟨ f , g ⟩ ∘ h)  ≈⟨ symEq comp-assoc ⟩
            (π₂ ∘ ⟨ f , g ⟩) ∘ h  ≈⟨ comp-congˡ β₂    ⟩
            g ∘ h                 ∎)

      extensionality : Extensionality
      extensionality {h = h} {h' = h'} e1 e2 = begin
        h                                    ≈⟨ pair-extensionality e1 e2 ⟩
        ⟨ π₁ ∘ h' , π₂ ∘ h' ⟩                ≈⟨ symEq pair-comp           ⟩
        ⟨ π₁ , π₂ ⟩ ∘ h'                     ≈⟨ comp-congˡ (symEq η)      ⟩
        id _ ∘ h'                            ≈⟨ comp-id-l                 ⟩
        h'                                   ∎

      pair-cong : PairCong
      pair-cong {f = f} {f' = f'} {g = g} {g' = g'} ef eg = pair-extensionality
        (begin
          π₁ ∘ ⟨ f , g ⟩ ≈⟨ β₁ ⟩
          f              ≈⟨ ef ⟩
          f'             ∎)
        (begin
          π₂ ∘ ⟨ f , g ⟩ ≈⟨ β₂ ⟩
          g              ≈⟨ eg ⟩
          g'             ∎)

    module ExtensionalityConsequences (extensionality : Extensionality) where

      pair-extensionality : PairExtensionality
      pair-extensionality {f = f} {g = g} {h = h} e1 e2 = extensionality
        (begin
          π₁ ∘ h         ≈⟨ e1 ⟩
          f              ≈⟨ symEq β₁ ⟩
          π₁ ∘ ⟨ f , g ⟩ ∎)
        (begin
          π₂ ∘ h         ≈⟨ e2 ⟩
          g              ≈⟨ symEq β₂ ⟩
          π₂ ∘ ⟨ f , g ⟩ ∎)

    module EtaPermuationConsequences (η : Eta) (pair-comp : PairComp) (pair-cong : PairCong) where

      pair-extensionality : PairExtensionality
      pair-extensionality {f = f} {g = g} {h = h} e1 e2 = begin
        h                                               ≈⟨ symEq comp-id-l ⟩
        id _ ∘ h                                        ≈⟨ comp-congˡ η ⟩
        ⟨ π₁ , π₂ ⟩ ∘ h                                 ≈⟨ pair-comp ⟩
        ⟨ π₁ ∘ h , π₂ ∘ h ⟩                             ≈⟨ pair-cong e1 e2 ⟩
        ⟨ f , g ⟩ ∎



  module ProductAPI (P : Product) where

    open WeakProductAPI (weakTerminalObject P) public
    open Terminal (P .terminal) public using () renaming (!-unique to pair-universal)

    -- The universal property for pairing.

    module _ {C : Obj} {f : Hom C A} {g : Hom C B} {h : Hom C A×B} where
      open ConeHom

      pair-extensionality
        : π₁ ∘ h ≈ f
        → π₂ ∘ h ≈ g
        →      h ≈ ⟨ f , g ⟩

      pair-extensionality ef eg = pair-universal λ where
          .coneHom   → h
          .tri false → ef
          .tri true  → eg

    open UniversalityConsequences pair-extensionality public

{-

    -- The eta-law.

    η : id A×B ≈ ⟨ π₁ , π₂ ⟩
    η = pair-extensionality comp-id-r comp-id-r

    -- The permutation law.

    module _ {C : Obj} {f : Hom C A} {g : Hom C B} {D : Obj} {h : Hom D C} where
      open EqReasoning

      pair-comp : ⟨ f , g ⟩ ∘ h ≈ ⟨ f ∘ h , g ∘ h ⟩
      pair-comp = pair-extensionality
          (begin
            π₁ ∘ (⟨ f , g ⟩ ∘ h)  ≈⟨ symEq comp-assoc ⟩
            (π₁ ∘ ⟨ f , g ⟩) ∘ h  ≈⟨ comp-congˡ β₁    ⟩
            f ∘ h                 ∎)
          (begin
            π₂ ∘ (⟨ f , g ⟩ ∘ h)  ≈⟨ symEq comp-assoc ⟩
            (π₂ ∘ ⟨ f , g ⟩) ∘ h  ≈⟨ comp-congˡ β₂    ⟩
            g ∘ h                 ∎)


{-
    open Cone     (P .𝟙)        public using () renaming (Src to A×B; cone to π)
    open Terminal (P .terminal) public using () renaming (! to pairConeHom; !-unique to pair-universal)
    module _ (sp : Span) where
      open ConeHom (pairConeHom sp) public using () renaming (coneHom to pair)
    module _ {sp : Span} where
      open ConeHom (pairConeHom sp) public using () renaming (tri to β)

    π₁ = π false
    π₂ = π true

    module _ {C : Obj} (f : Hom C A) (g : Hom C B) where

      span : Span
      span .Cone.Src = _
      span .Cone.cone false = f
      span .Cone.cone true  = g
      span .Cone.coh  refl  = comp-id-l

      ⟨_,_⟩ :  Hom C A×B
      ⟨_,_⟩ = pair span


    module _ {C : Obj} {f : Hom C A} {g : Hom C B} where

      β₁ : π₁ ∘ ⟨ f , g ⟩ ≈ f
      β₁ = β false

      β₂ : π₂ ∘ ⟨ f , g ⟩ ≈ g
      β₂ = β true

    -- foo = {!pair !}

-- foo = {!TerminalObject!}

{-

Product : ∀ {A B : Obj} (r : Relation A B) → Set _
Product r = Limit
  where open Limits (r .Relation.theSpan)

module _ {A B : Obj} where

  ⟨_,_⟩ : ∀{A B C : Obj} (f : Hom C A) (g : Hom C B) → Hom


IsProduct : ∀ {A B : Obj} (r : Relation A B) → Set _
IsProduct r = {! IsLimit !}
  where open Limits (r .Relation.theSpan)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
