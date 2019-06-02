{-# OPTIONS --postfix-projections #-}

open import Library
open import Category

module Category.Span where

-- A span is a diagram over the index category - ← o → +.

SpanIndex : Category lzero lzero lzero
SpanIndex = record
  { SpanIndexCategory
  ; id         = λ A → Hom.id {A}
  ; comp-assoc = λ {A} {B} {C} {D} {f} {g} {h} → comp-assoc {A} {B} {C} {D} {f} {g} {h}
  }
  module SpanIndexCategory where

    data Obj : Set where
      - o + : Obj

    data Hom : (A B : Obj) → Set where
      id : {A : Obj} → Hom A A
      -  : Hom o -
      +  : Hom o +

    HomS : (A B : Obj) → Setoid lzero lzero
    HomS A B = setoid (Hom A B)

    comp : ∀{A B C} → Hom B C → Hom A B → Hom A C
    comp id f = f
    comp g id = g

    comp-id-l : ∀{A B} {f : Hom A B} → comp id f ≡ f
    comp-id-l = refl

    comp-id-r : ∀{A B} {f : Hom A B} → comp f id ≡ f
    comp-id-r {f = id} = refl
    comp-id-r {f = - } = refl
    comp-id-r {f = + } = refl

    comp-assoc : ∀{A B C D : Obj} {f : Hom C D} {g : Hom B C} {h : Hom A B}
      → comp (comp f g) h ≡ comp f (comp g h)
    comp-assoc {f = id}          = refl
    comp-assoc {f = - } {g = id} = refl
    comp-assoc {f = + } {g = id} = refl

    comp-cong : ∀{A B C : Obj} {f f' : Hom B C} {g g' : Hom A B}
      → f ≡ f'
      → g ≡ g'
      → comp f g ≡ comp f' g'
    comp-cong = cong₂ comp

module _ {ℓₒ ℓₕ ℓₑ} where

  Span : (C : Category ℓₒ ℓₕ ℓₑ) → Set _
  Span C = Functor SpanIndex C

  module Span {C : Category ℓₒ ℓₕ ℓₑ} where

    open Category.Category C
    open SpanIndexCategory using (-; +; o) renaming (Obj to I; Hom to J)
    open Functor

    -- Construct a span from two morphisms f : R ⇒ A and g : R ⇒ B

    module _ {A B R : Obj} (f : Hom R A) (g : Hom R B) where

      span : Span C
      span .App I.-      = A
      span .App I.o      = R
      span .App I.+      = B
      span .map J.id     = id _
      span .map J.-      = f
      span .map J.+      = g
      span .map-id                     = reflEq
      span .map-comp {f = J.id}        = symEq comp-id-l
      span .map-comp {f = J.- } {J.id} = symEq comp-id-r
      span .map-comp {f = J.+ } {J.id} = symEq comp-id-r
      span .map-cong refl              = reflEq

    -- A relation between two objects A and B is a span A ⇐ R ⇒ B

    record Relation (A B : Obj) : Set (ℓₒ ⊔ ℓₕ ⊔ ℓₑ) where
      field
        theSpan : Span C
        fix-    : theSpan .App I.- ≡ A
        fix+    : theSpan .App I.- ≡ B

{-
    span A R B = record{M}
      module M where
        App : I → Obj
        App I.- = A
        App I.o = R
        App I.+ = B

{-
    span A R B .Functor.App = {!!}
    span A R B .Functor.map = {!!}
    span A R B .Functor.map-id = {!!}
    span A R B .Functor.map-comp = {!!}
    span A R B .Functor.map-cong = {!!}

-- -}
-- -}
-- -}
