{-# OPTIONS --postfix-projections #-}

module Library where

open import Level public using (Level; _⊔_; Lift; lift; lower)
  renaming (zero to lzero; suc to lsuc)

open import Data.Bool.Base  public using (Bool; true; false) hiding (module Bool)
open import Data.List.Base  public using (List; []; _∷_)

open import Data.Empty      public using (⊥; ⊥-elim)

open import Data.Unit       public using (⊤)
open import Data.Product    public using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
                            public using (×-setoid)

open import Function as Fun   public using (_∘′_)
open import Function.Equality public using (_⇨_; _⟨$⟩_)
module Function = Fun
module FEq = Function.Equality

open import Relation.Binary public using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl; sym; trans; subst; subst₂)
module PEq = Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid
module SetoidReasoning = Relation.Binary.Reasoning.Setoid

⊥-setoid : ∀ o e → Setoid o e
⊥-setoid o e .Setoid.Carrier = Lift _ ⊥
⊥-setoid o e .Setoid._≈_ _ _ = Lift _ ⊥
⊥-setoid o e .Setoid.isEquivalence .IsEquivalence.refl {x = ()}
⊥-setoid o e .Setoid.isEquivalence .IsEquivalence.sym ()
⊥-setoid o e .Setoid.isEquivalence .IsEquivalence.trans ()

⊤-setoid : ∀ o e → Setoid o e
⊤-setoid o e .Setoid.Carrier = Lift _ ⊤
⊤-setoid o e .Setoid._≈_ _ _ = Lift _ ⊤
⊤-setoid o e .Setoid.isEquivalence = _

Π-setoid : ∀ {i o e} {I : Set i} (S : I → Setoid o e) → Setoid (i ⊔ o) (i ⊔ e)
Π-setoid S .Setoid.Carrier                               = ∀ i → S i .Setoid.Carrier
Π-setoid S .Setoid._≈_ s t                               = ∀ i → S i .Setoid._≈_ (s i) (t i)
Π-setoid S .Setoid.isEquivalence .IsEquivalence.refl         i = S i .Setoid.refl
Π-setoid S .Setoid.isEquivalence .IsEquivalence.sym   eq     i = S i .Setoid.sym   (eq i)
Π-setoid S .Setoid.isEquivalence .IsEquivalence.trans eq eq' i = S i .Setoid.trans (eq i) (eq' i)

-- A variant of Π-setoid with hidden quantification.

∀-setoid : ∀ {i o e} {I : Set i} (S : I → Setoid o e) → Setoid (i ⊔ o) (i ⊔ e)
∀-setoid S .Setoid.Carrier                                    = ∀{i} → S i .Setoid.Carrier
∀-setoid S .Setoid._≈_ s t                                    = ∀{i} → S i .Setoid._≈_ (s {i}) (t {i})
∀-setoid S .Setoid.isEquivalence .IsEquivalence.refl         {i = i} = S i .Setoid.refl
∀-setoid S .Setoid.isEquivalence .IsEquivalence.sym   eq     {i = i} = S i .Setoid.sym   (eq {i})
∀-setoid S .Setoid.isEquivalence .IsEquivalence.trans eq eq' {i = i} = S i .Setoid.trans (eq {i}) (eq' {i})

Σ-setoid : ∀ {i o e} {I : Set i} (S : I → Setoid o e) → Setoid (i ⊔ o) (i ⊔ e)

Σ-setoid S .Setoid.Carrier             = ∃         λ i   → S i .Setoid.Carrier
Σ-setoid S .Setoid._≈_ (i , s) (j , t) = Σ (i ≡ j) λ i≡j → S j .Setoid._≈_ (subst _ i≡j s) t

Σ-setoid S .Setoid.isEquivalence .IsEquivalence.refl               = refl , S _ .Setoid.refl
Σ-setoid S .Setoid.isEquivalence .IsEquivalence.sym   (refl , eq)  = refl , S _ .Setoid.sym eq
Σ-setoid S .Setoid.isEquivalence .IsEquivalence.trans (refl , eq)
                                                      (refl , eq') = refl , S _ .Setoid.trans eq eq'

module Bool where

  data _≤_ : Bool → Bool → Set where
    false≤true : false ≤ true
    refl-≤     : ∀{b} → b ≤ b

  trans-≤ : ∀{a b c} → a ≤ b → b ≤ c → a ≤ c
  trans-≤ refl-≤ q = q
  trans-≤ p refl-≤ = p
