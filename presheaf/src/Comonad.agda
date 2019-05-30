{-# OPTIONS --postfix-projections #-}

open import Library
open import Category

module Comonad where

-- A comonad in category C consists of the following data:

record Comonad {o h e} (C : Category o h e) : Set (o ⊔ h ⊔ e) where

  open Category.Category C -- using (id; module EqReasoning)
    renaming (Hom to _⇒_; Eq to _≈_; comp to _∘_)
  open EqReasoning

  -- 1. An endofunctor W on C.

  field
    functor : EndoFunctor C
  open Functor functor public
  open Functor functor using () renaming (App to W)

  -- 2. A natural transformation  ε/extract   : W → Id.
  -- 3. A natural transformation  δ/duplicate : W → W ∘ W.

  field
    ε : NaturalTransformation functor (idFun C)
    δ : NaturalTransformation functor (compFun functor functor)

  open NaturalTransformation ε public using () renaming
    ( transformation to extract
    ; naturality⁻¹   to extract∘map
    )

  -- Unit:
  -- extract       : W A ⇒ A
  -- extract∘map f : extract ∘ map f ≈ f ∘ extract

  open NaturalTransformation δ public using () renaming
    ( transformation to duplicate
    ; naturality⁻¹   to duplicate∘map
    )

  -- Multiplication:
  -- duplicate       : W A ⇒ W (W A)
  -- duplicate∘map f : duplicate ∘ map f ≈ map (map f) ∘ duplicate

  -- 4. The following laws how extract and duplicate interact.

  field
    -- Outer counit.
    extract∘duplicate       : ∀{A} → extract ∘ duplicate ≈ id (W A)                        -- β law
    -- Inner counit.
    map-extract∘duplicate   : ∀{A} → map extract ∘ duplicate ≈ id (W A)                    -- η law
    -- Two ways to inflate.
    map-duplicate∘duplicate : ∀{A} → map duplicate ∘ duplicate ≈ duplicate ∘ duplicate {A} -- assoc law

  -- Comonadic extension.

  extend : ∀{A B} → W A ⇒ B → W A ⇒ W B
  extend f = map f ∘ duplicate

  extend-cong : ∀{A B} {f g : W A ⇒ B} → f ≈ g → extend f ≈ extend g
  extend-cong f≈g = comp-congˡ (map-cong f≈g)

  -- Co-Kleisli composition.

  _=<=_ : ∀{A B C} → W B ⇒ C → W A ⇒ B → W A ⇒ C
  g =<= f = g ∘ extend f

  -- Co-Kleisli forward composition.

  _=>=_ : ∀{A B C} → W A ⇒ B → W B ⇒ C → W A ⇒ C
  f =>= g = g =<= f

  -- Laws for the Co-Kleisli composition.

  -- β: extract is right unit of =>=.

  beta : ∀{A B} {f : W A ⇒ B} → (f =>= extract) ≈ f
  beta {A} {B} {f} = begin
    f =>= extract                  ≡⟨⟩
    extract ∘ extend f             ≡⟨⟩
    extract ∘ (map f ∘ duplicate)  ≈⟨ symEq comp-assoc ⟩
    (extract ∘ map f) ∘ duplicate  ≈⟨ comp-congˡ (symEq (extract∘map f)) ⟩
    (f ∘ extract) ∘ duplicate      ≈⟨ comp-assoc ⟩
    f ∘ (extract ∘ duplicate)      ≈⟨ comp-congʳ extract∘duplicate ⟩
    f ∘ id _                       ≈⟨ comp-id-r ⟩
    f ∎

  -- η: extract is left unit of >=>.

  eta : ∀{A B} {f : W A ⇒ B} → (extract =>= f) ≈ f
  eta {A} {B} {f} = begin
    extract =>= f                  ≡⟨⟩
    f ∘ extend extract             ≡⟨⟩
    f ∘ (map extract ∘ duplicate)  ≈⟨ comp-congʳ map-extract∘duplicate ⟩
    f ∘ id _                       ≈⟨ comp-id-r ⟩
    f ∎

  -- Extend Lemma.

  extend-∘extend : ∀{A B C} {f : W B ⇒ C} {g : W A ⇒ B} →

    extend (f ∘ extend g)  ≈  extend f ∘ extend g

  extend-∘extend {A} {B} {C} {f} {g} =                     begin

    extend (f ∘ extend g)                                  ≡⟨⟩
    map (f ∘ (map g ∘ duplicate)) ∘ duplicate              ≈⟨ comp-congˡ map-comp ⟩
    (map f ∘ map (map g ∘ duplicate)) ∘ duplicate          ≈⟨ comp-congˡ (comp-congʳ map-comp) ⟩
    (map f ∘ (map (map g) ∘ map duplicate)) ∘ duplicate    ≈⟨ comp-assoc ⟩
    map f ∘ ((map (map g) ∘ map duplicate) ∘ duplicate)    ≈⟨ comp-congʳ comp-assoc ⟩
    map f ∘ (map (map g) ∘ (map duplicate ∘ duplicate))    ≈⟨ comp-congʳ (comp-congʳ map-duplicate∘duplicate) ⟩
    map f ∘ (map (map g) ∘ (duplicate ∘ duplicate))        ≈⟨ comp-congʳ (symEq comp-assoc) ⟩
    map f ∘ ((map (map g) ∘ duplicate) ∘ duplicate)        ≈⟨ comp-congʳ (comp-congˡ (duplicate∘map _)) ⟩
    map f ∘ ((duplicate ∘ map g) ∘ duplicate)              ≈⟨ comp-congʳ comp-assoc ⟩
    map f ∘ (duplicate ∘ (map g ∘ duplicate))              ≈⟨ symEq comp-assoc ⟩
    (map f ∘ duplicate) ∘ (map g ∘ duplicate)              ≡⟨⟩
    extend f ∘ extend g                                    ∎

  -- Associativity of =>=.

  assoc : ∀{A B C D} {f : W A ⇒ B} {g} {h : W C ⇒ D} →

    (f =>= g) =>= h  ≈  f =>= (g =>= h)

  assoc {A} {B} {C} {D} {f} {g} {h} = begin
    (f =>= g) =>= h                   ≡⟨⟩
    h ∘ extend (g ∘ extend f)         ≈⟨ comp-congʳ extend-∘extend ⟩
    h ∘ (extend g ∘ extend f)         ≈⟨ symEq comp-assoc ⟩
    (h ∘ extend g) ∘ extend f         ≡⟨⟩
    f =>= (g =>= h)                   ∎

-- -}
-- -}
-- -}
-- -}
