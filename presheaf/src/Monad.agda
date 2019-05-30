{-# OPTIONS --postfix-projections #-}

open import Library
open import Category

module Monad where

-- A monad in category C consists of the following data:

record Monad {o h e} (C : Category o h e) : Set (o ⊔ h ⊔ e) where

  open Category.Category C -- using (id; module EqReasoning)
    renaming (Hom to _⇒_; Eq to _≈_; comp to _∘_)
  open EqReasoning

  -- An endofunctor M on C.

  field
    functor : EndoFunctor C
  open Functor functor public
  open Functor functor using () renaming (App to M)

  -- A natural transformation  η/return : Id → M.
  -- A natural transformation  μ/join   : M ∘ M → M.

  field
    η : NaturalTransformation (idFun C) functor
    μ : NaturalTransformation (compFun functor functor) functor

  open NaturalTransformation η public using () renaming
    ( transformation to return
    ; naturality⁻¹   to map∘return
    )

  -- Unit:
  -- return       : A ⇒ M A
  -- map∘return f : map f ∘ return ≈ return ∘ f

  open NaturalTransformation μ public using () renaming
    ( transformation to join
    ; naturality⁻¹   to map∘join
    )

  -- Multiplication:
  -- join       : M (M A) ⇒ M A
  -- map∘join f : map f ∘ join ≈ join ∘ map (map f)


  -- The full types:
  -- return     : ∀{A} → A ⇒ M A
  -- map∘return : ∀{A B} {f : A ⇒ B} → map f ∘ return ≈ return ∘ f
  -- join     : ∀{A} → M (M A) ⇒ M A
  -- map∘join : ∀{A B} {f : A ⇒ B} → map f ∘ join ≈ join ∘ map (map f)


  -- Such that: return is the unit for join and join is associative.

  field
    -- Outer unit.
    join∘return     : ∀{A} → join ∘ return     ≈ id (M A)             -- β law: id † ∘ return = id
    -- Inner unit.
    join∘map-return : ∀{A} → join ∘ map return ≈ id (M A)             -- η law: return † = id
    -- Two ways the cookie crumbles.
    join∘map-join   : ∀{A} → join ∘ map join   ≈ join ∘ join {M A}    -- assoc law

  -- Monadic extension.

  _† : ∀{A B} → A ⇒ M B → M A ⇒ M B
  f † = join ∘ map f

  †-cong : ∀{A B} {f g : A ⇒ M B} → f ≈ g → (f †) ≈ (g †)
  †-cong f≈g = comp-congʳ (map-cong f≈g)

  -- Kleisli composition.

  _<=<_ : ∀{A B C} → B ⇒ M C → A ⇒ M B → A ⇒ M C
  g <=< f = (g †) ∘ f

  -- Kleisli forward composition.

  _>=>_ : ∀{A B C} → A ⇒ M B → B ⇒ M C → A ⇒ M C
  f >=> g = g <=< f

  -- Laws for the Kleisli composition.

  -- β: return is left unit of >=>.

  beta : ∀{A B} {f : A ⇒ M B} → (return >=> f) ≈ f
  beta {A} {B} {f} = begin
    return >=> f             ≡⟨⟩
    (f †) ∘ return           ≡⟨⟩
    (join ∘ map f) ∘ return  ≈⟨ comp-assoc  ⟩
    join ∘ (map f ∘ return)  ≈⟨ comp-congʳ (map∘return f) ⟩
    join ∘ (return ∘ f)      ≈⟨ symEq comp-assoc ⟩
    (join ∘ return) ∘ f      ≈⟨ comp-congˡ join∘return ⟩
    id _ ∘ f                 ≈⟨ comp-id-l ⟩
    f ∎

  -- η: return is right unit of >=>.

  eta : ∀{A B} {f : A ⇒ M B} → (f >=> return) ≈ f
  eta {A} {B} {f} = begin
    f >=> return             ≡⟨⟩
    (return †) ∘ f           ≡⟨⟩
    (join ∘ map return) ∘ f  ≈⟨ comp-congˡ join∘map-return ⟩
    id _ ∘ f                 ≈⟨ comp-id-l ⟩
    f ∎

  -- WRONG:
  -- map∘dagger : ∀{A B C} {f : B ⇒ M C} {g : A ⇒ M B} →
  --   map f ∘ (g †) ≈ map (f †) ∘ g


  dagger∘dagger : ∀{A B C} {f : B ⇒ M C} {g : A ⇒ M B} →

    (f †) ∘ (g †)  ≈  ((f †) ∘ g) †

  dagger∘dagger {A} {B} {C} {f} {g} = begin
    (f †) ∘ (g †)                             ≡⟨⟩
    (join ∘ map f) ∘ (join ∘ map g)           ≈⟨ comp-assoc ⟩
    join ∘ (map f ∘ (join ∘ map g))           ≈⟨ comp-congʳ (symEq comp-assoc) ⟩
    join ∘ ((map f ∘ join) ∘ map g)           ≈⟨ comp-congʳ (comp-congˡ (map∘join f)) ⟩
    join ∘ ((join ∘ map (map f)) ∘ map g)     ≈⟨ comp-congʳ comp-assoc ⟩
    join ∘ (join ∘ (map (map f) ∘ map g))     ≈⟨ symEq comp-assoc ⟩
    (join ∘ join) ∘ (map (map f) ∘ map g)     ≈⟨ comp-cong (symEq join∘map-join) (symEq map-comp) ⟩
    (join ∘ map join) ∘ (map (map f ∘ g))     ≈⟨ comp-assoc ⟩
    join ∘ (map join ∘ (map (map f ∘ g)))     ≈⟨ comp-congʳ (symEq map-comp) ⟩
    join ∘ map (join ∘ (map f ∘ g))           ≈⟨ comp-congʳ (map-cong (symEq comp-assoc)) ⟩
    join ∘ map ((join ∘ map f) ∘ g)           ≡⟨⟩
    ((f †) ∘ g) † ∎

  -- Associativity of >=>.

  assoc : ∀{A B C D} {f : A ⇒ M B} {g} {h : C ⇒ M D} →

    (f >=> g) >=> h  ≈  f >=> (g >=> h)

  assoc {A} {B} {C} {D} {f} {g} {h} = begin
    (f >=> g) >=> h        ≡⟨⟩
    (h †) ∘ ((g †) ∘ f)    ≈⟨ symEq comp-assoc ⟩
    ((h †) ∘ (g †)) ∘ f    ≈⟨ comp-congˡ dagger∘dagger ⟩
    (((h †) ∘ g) †) ∘ f    ≡⟨⟩
    f >=> (g >=> h) ∎

-- -}
-- -}
-- -}
-- -}
