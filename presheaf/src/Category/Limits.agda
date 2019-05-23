{-# OPTIONS --postfix-projections #-}

open import Library
open import Category

module Category.Limits where

-- Fix an index category and a target category and a diagram F

module Limits
         {oi hi ei} {I : Category oi hi ei}
         {o  h  e } {C : Category o  h  e }
         (F : Functor I C) where
  open Category.Category
  open Functor

  _∘_  = C .comp
  _≈_  = C .Eq
  _≤_  = I .Hom
  fmap = F .map

  -- A cone has arrows pointing from the source down to the base

  record Cone : Set (o ⊔ h ⊔ e ⊔ oi ⊔ hi) where
    field
      Src  : C .Obj
      cone : ∀ i → C .Hom Src (F .App i)
    field
      coh  : ∀{i j} (f : i ≤ j) → (fmap f ∘ cone i) ≈ cone j

  -- A cone morphism is a morphism between the sources

  module _ (K L : Cone) where
    open Cone K using () renaming (Src to S; cone to ψ)
    open Cone L using () renaming (Src to T; cone to ϕ)

    record ConeHom : Set (h ⊔ e ⊔ oi) where
      field
        coneHom : C .Hom S T
      field
        tri : ∀ i → (ϕ i ∘ coneHom) ≈ ψ i
    open ConeHom public

    ConeHomS :  Setoid (oi ⊔ h ⊔ e) e
    ConeHomS .Setoid.Carrier = ConeHom
    ConeHomS .Setoid._≈_ U V = U .coneHom ≈ V .coneHom
    ConeHomS .Setoid.isEquivalence .IsEquivalence.refl  = C .reflEq
    ConeHomS .Setoid.isEquivalence .IsEquivalence.sym   = C .symEq
    ConeHomS .Setoid.isEquivalence .IsEquivalence.trans = C .transEq

  -- Cone morphisms form a category

  idConeHom : ∀ K → ConeHom K K
  idConeHom K .coneHom = C .id _
  idConeHom K .tri  i  = C .comp-id-r

  module _ {K L M} (U : ConeHom L M) (V : ConeHom K L) where
    u = U .coneHom
    v = V .coneHom

    compConeHom : ConeHom K M
    compConeHom .coneHom = u ∘ v
    compConeHom .tri i   = begin
        M .cone i ∘ (u ∘ v)  ≈⟨ C .symEq (C .comp-assoc) ⟩
        (M .cone i ∘ u) ∘ v  ≈⟨ C .comp-cong (U .tri i) (C .reflEq) ⟩
        L .cone i ∘ v        ≈⟨ V .tri i ⟩
        K .cone i ∎
      where
      open Cone
      open SetoidReasoning (C .HomS _ _)

  CONE : Category (oi ⊔ hi ⊔ o ⊔ h ⊔ e) (oi ⊔ h ⊔ e) e
  CONE .Obj  = Cone
  CONE .HomS = ConeHomS
  CONE .id   = idConeHom
  CONE .comp = compConeHom
  CONE .comp-id-l  = C .comp-id-l
  CONE .comp-id-r  = C .comp-id-r
  CONE .comp-assoc = C .comp-assoc
  CONE .comp-cong  = C .comp-cong

  -- A limit of a diagram is its terminal cone.

  open Finality
  Limit = TerminalObject CONE


-- Dualize everything to get colimits

module Colimits
         {oi hi ei} {I : Category oi hi ei}
         {o  h  e } {C : Category o  h  e }
         (F : Functor I C) where
