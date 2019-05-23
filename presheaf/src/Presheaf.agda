{-# OPTIONS --postfix-projections #-}

open import Library
open import Category

module Presheaf where

-- Presheaves over C are contravariant functors from C to SET

Presheaf : ∀ o e {o1 h1 e1} (C : Category o1 h1 e1) → Set (lsuc (o ⊔ e) ⊔ o1 ⊔ h1 ⊔ e1)
Presheaf o e C = Functor (op C) (SET o e)

-- Empty presheaf

⊥-presheaf : ∀ o e {o1 h1 e1} (C : Category o1 h1 e1) → Presheaf o e C
⊥-presheaf o e C .App _ = ⊥-setoid o e
⊥-presheaf o e C .map f ._⟨$⟩_ ()
⊥-presheaf o e C .map f .FEq.cong ()
⊥-presheaf o e C .map-id ()
⊥-presheaf o e C .map-comp ()
⊥-presheaf o e C .map-cong eq ()

-- Unit presheaf

⊤-presheaf : ∀ o e {o1 h1 e1} (C : Category o1 h1 e1) → Presheaf o e C
⊤-presheaf o e _ .App _    = ⊤-setoid o e
⊤-presheaf o e _ .map _    = _
⊤-presheaf o e _ .map-id   = _
⊤-presheaf o e _ .map-comp = _
⊤-presheaf o e _ .map-cong = _

-- Binary presheaf constructions

module _ {o e o1 h1 e1} {C : Category o1 h1 e1}
         (P Q : Presheaf o e C) where

  -- Binary presheaf product

  ×-presheaf : Presheaf o e C

  ×-presheaf .App A                         = ×-setoid (P .App A) (Q .App A)
  ×-presheaf .map f ._⟨$⟩_    (p    , q   ) = P .map f ⟨$⟩ p
                                            , Q .map f ⟨$⟩ q
  ×-presheaf .map f .FEq.cong (p=p' , q=q') = P .map f .FEq.cong p=p'
                                            , Q .map f .FEq.cong q=q'
  ×-presheaf .map-id          (p=p' , q=q') = P .map-id p=p'
                                            , Q .map-id q=q'
  ×-presheaf .map-comp        (p=p' , q=q') = P .map-comp p=p' , Q .map-comp q=q'
  ×-presheaf .map-cong f=f'   (p=p' , q=q') = P .map-cong f=f' p=p'
                                            , Q .map-cong f=f' q=q'

  -- Presheaf exponential

  private
    Fun : (Δ : C .Obj) → Setoid (o ⊔ e) (o ⊔ e)
    Fun Δ = P .App Δ ⇨ Q .App Δ

  -- Kripke function space on setoids

  KFun : (Γ : C .Obj) → Setoid (o ⊔ e ⊔ o1 ⊔ h1 ⊔ e1) (o ⊔ e ⊔ o1 ⊔ h1 ⊔ e1)
  KFun Γ = ∀-setoid λ Δ → C .HomS Δ Γ ⇨ (P .App Δ ⇨ Q .App Δ)

  →-presheaf : Presheaf (o ⊔ e ⊔ o1 ⊔ h1 ⊔ e1) (o ⊔ e ⊔ o1 ⊔ h1 ⊔ e1) C
  →-presheaf .App = KFun
  →-presheaf .map f ._⟨$⟩_     ϕ   {Δ} ._⟨$⟩_    g         =  ϕ   {Δ} ⟨$⟩       (C .comp f g)
  →-presheaf .map f ._⟨$⟩_     ϕ   {Δ} .FEq.cong g=g' x=y  =  ϕ   {Δ} .FEq.cong (C .comp-cong (C .reflEq) g=g') x=y
  →-presheaf .map f .FEq.cong  ϕ=ψ {Δ}           g=g' x=y  =  ϕ=ψ {Δ}           (C .comp-cong (C .reflEq) g=g') x=y

  →-presheaf .map-id {Γ}{ϕ}{ψ} ϕ=ψ {Δ} {g} {g'}  g=g' x=y  =  ϕ=ψ {Δ}          (C .transEq (C .comp-id-l) g=g') x=y

  →-presheaf .map-comp         ϕ=ψ {Δ}           g=g' x=y  =  ϕ=ψ {Δ} (C .transEq (C .comp-cong (C .reflEq) g=g') (C .comp-assoc)) x=y
  →-presheaf .map-cong f=f'    ϕ=ψ {Δ}           g=g' x=y  =  ϕ=ψ {Δ} (C .comp-cong f=f' g=g') x=y


  -- →-presheaf : Presheaf (o ⊔ e ⊔ o1 ⊔ h1) (o ⊔ e ⊔ o1 ⊔ h1) C
  -- →-presheaf .App Γ .Setoid.Carrier = ∀ {Δ} (g : C .Hom Δ Γ) → Fun Δ .Setoid.Carrier
  -- →-presheaf .App Γ .Setoid._≈_ ϕ ψ = ∀ {Δ} (g : C .Hom Δ Γ) → Fun Δ .Setoid._≈_ (ϕ g) (ψ g)
  -- →-presheaf .App Γ .Setoid.isEquivalence .IsEquivalence.refl  {ϕ}              {Δ} g x=y = Fun Δ .Setoid.refl {ϕ g} x=y
  -- →-presheaf .App Γ .Setoid.isEquivalence .IsEquivalence.sym   {ϕ}{ψ}    eq     {Δ} g x=y = Fun Δ .Setoid.sym  {ϕ g} {ψ g} (eq g) x=y
  -- →-presheaf .App Γ .Setoid.isEquivalence .IsEquivalence.trans {ϕ}{ψ}{ξ} eq eq' {Δ} g x=y = Fun Δ .Setoid.trans {ϕ g} {ψ g} {ξ g} (eq g) (eq' g) x=y

  -- →-presheaf .map f ._⟨$⟩_    ϕ   g     = ϕ   (C .comp f g)
  -- →-presheaf .map f .FEq.cong ϕ=ψ g x=y = ϕ=ψ (C .comp f g) x=y
  -- →-presheaf .map-id {Γ} {ϕ} {ψ} ϕ=ψ {Δ} g {x} {y} x=y = begin
  --     (ϕ (C .comp (C .id Γ) g) ⟨$⟩ x) ≈⟨ {!C .comp-id-l !} ⟩
  --     (ϕ g ⟨$⟩ x)                     ≈⟨ ϕ=ψ g x=y ⟩
  --     (ψ g ⟨$⟩ y)                     ∎
  --   where
  --   open SetoidReasoning (Q .App Δ)
  -- →-presheaf .map-comp = {!!}
  -- →-presheaf .map-cong = {!!}


-- I-ary presheaf product

Π-presheaf : ∀ {i o e o1 h1 e1} {I : Set i} {C : Category o1 h1 e1}
           → (P : I → Presheaf o e C)
           → Presheaf (i ⊔ o) (i ⊔ e) C

Π-presheaf P .App A = Π-setoid λ i → P i .App A
Π-presheaf P .map f ._⟨$⟩_    a  i = P i .map f ⟨$⟩ a i
Π-presheaf P .map f .FEq.cong eq i = P i .map f .FEq.cong (eq i)
Π-presheaf P .map-id          eq i = P i .map-id          (eq i)
Π-presheaf P .map-comp        eq i = P i .map-comp        (eq i)
Π-presheaf P .map-cong f=f'   eq i = P i .map-cong f=f'   (eq i)

-- I-ary presheaf sum

Σ-presheaf : ∀ {i o e o1 h1 e1} {I : Set i} {C : Category o1 h1 e1}
           → (P : I → Presheaf o e C)
           → Presheaf (i ⊔ o) (i ⊔ e) C
Σ-presheaf P .App A                       = Σ-setoid λ i → P i .App A
Σ-presheaf P .map f ⟨$⟩       (i    , p ) = i    , P i .map f ⟨$⟩ p
Σ-presheaf P .map f .FEq.cong (refl , eq) = refl , P _ .map f .FEq.cong eq
Σ-presheaf P .map-id          (refl , eq) = refl , P _ .map-id   eq
Σ-presheaf P .map-comp        (refl , eq) = refl , P _ .map-comp eq
Σ-presheaf P .map-cong f=f'   (refl , eq) = refl , P _ .map-cong f=f' eq

-- Presheaf category

presheaf-cat : ∀ s {o h e}    (let ℓ = s ⊔ o ⊔ h ⊔ e)
               → (C : Category o h e)
               → Category (lsuc ℓ) (lsuc ℓ) ℓ
presheaf-cat s {o} {h} {e} C = let ℓ = s ⊔ o ⊔ h ⊔ e in

  functor-cat (op C) (SET ℓ ℓ)

-- projᵢ and injᵢ are natural transformations on presheafs

module _ {i o e o1 h1 e1} {I : Set i} {C : Category o1 h1 e1}
         (P : I → Presheaf (i ⊔ o) (i ⊔ e) C) where

  -- Projection from presheaf product is natural

  proj-presheaf : ∀ i → NaturalTransformation (Π-presheaf P) (P i)
  proj-presheaf i .transformation A ⟨$⟩        p = p i
  proj-presheaf i .transformation A .FEq.cong eq = eq i
  proj-presheaf i .naturality f               eq = P i .map-cong (C .reflEq) (eq i)

  -- Injection into presheaf sum is natural

  inj-presheaf : ∀ i → NaturalTransformation (P i) (Σ-presheaf P)
  inj-presheaf i .transformation A ._⟨$⟩_     p = i , p
  inj-presheaf i .transformation A .FEq.cong eq = refl , eq
  inj-presheaf i .naturality f               eq = refl , P i .map-cong (C .reflEq) eq
