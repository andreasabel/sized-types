{-# OPTIONS --postfix-projections #-}

module Category.List where

open import Library
open import Category


-- Suggested instantiations of AllowWk
--
--   ⊤ : allow weakenings
--   ⊥ : do not allow weakenings
--

module PointwiseAllowExtension (AllowWk : Set) {o h e} (C : Category o h e) where

  AW    = AllowWk

  data _⊂_ : (Γ Δ : List (C .Obj)) → Set h where
    []   : [] ⊂ []
    wk   : ∀{Γ Δ} (a : AW) (B : C .Obj) (fs : Γ ⊂ Δ) → Γ       ⊂ (B ∷ Δ)
    _∷_  : ∀{A B Γ Δ}  (f : C .Hom A B) (fs : Γ ⊂ Δ) → (A ∷ Γ) ⊂ (B ∷ Δ)

  refl-⊂ : ∀ Γ → Γ ⊂ Γ
  refl-⊂ []      = []
  refl-⊂ (A ∷ Γ) = C .id A ∷ refl-⊂ Γ

  trans-⊂ : ∀{Γ Δ Φ} → Γ ⊂ Δ → Δ ⊂ Φ → Γ ⊂ Φ
  trans-⊂ fs        []       = fs
  trans-⊂ fs       (wk a B gs) = wk a B (trans-⊂ fs gs)
  trans-⊂ (wk a A fs) (g ∷ gs) = wk a _ (trans-⊂ fs gs)
  trans-⊂ (f  ∷ fs) (g ∷ gs) = C .comp g f ∷ (trans-⊂ fs gs)

  data Eq-⊂ : ∀{Γ Δ} (fs gs : Γ ⊂ Δ) → Set e where
    []  : Eq-⊂ [] []
    _∷_ : ∀{A B Γ Δ} {f g : C .Hom A B} {fs gs : Γ ⊂ Δ}
        → C .Eq f g → Eq-⊂ fs gs → Eq-⊂ (f ∷ fs) (g ∷ gs)
    wk  : ∀ a B {Γ Δ}  {fs gs : Γ ⊂ Δ}
        → Eq-⊂ fs gs → Eq-⊂ (wk a B fs) (wk a B gs)

  refl-Eq-⊂ : ∀{Γ Δ} (fs : Γ ⊂ Δ) → Eq-⊂ fs fs
  refl-Eq-⊂ []        = []
  refl-Eq-⊂ (wk a B fs) = wk a B (refl-Eq-⊂ fs)
  refl-Eq-⊂ (f ∷ fs)  = C .reflEq ∷ refl-Eq-⊂ fs

  sym-Eq-⊂ : ∀{Γ Δ} {fs gs : Γ ⊂ Δ} → Eq-⊂ fs gs → Eq-⊂ gs fs
  sym-Eq-⊂ []       = []
  sym-Eq-⊂ (e ∷ p)  = C .symEq e ∷ sym-Eq-⊂ p
  sym-Eq-⊂ (wk a B p) = wk a B (sym-Eq-⊂ p)

  trans-Eq-⊂ : ∀{Γ Δ} {fs gs hs : Γ ⊂ Δ}
             → Eq-⊂ fs gs → Eq-⊂ gs hs → Eq-⊂ fs hs
  trans-Eq-⊂ []       []         = []
  trans-Eq-⊂ (e ∷ p)  (e' ∷ p')  = C .transEq e e' ∷ trans-Eq-⊂ p p'
  trans-Eq-⊂ (wk a B p) (wk a .B p') = wk a B (trans-Eq-⊂ p p')

  ⊂-setoid : (Γ Δ : List (C .Obj)) → Setoid h e
  ⊂-setoid Γ Δ .Setoid.Carrier = Γ ⊂ Δ
  ⊂-setoid Γ Δ .Setoid._≈_ fs gs = Eq-⊂ fs gs
  ⊂-setoid Γ Δ .Setoid.isEquivalence .IsEquivalence.refl  = refl-Eq-⊂ _
  ⊂-setoid Γ Δ .Setoid.isEquivalence .IsEquivalence.sym   = sym-Eq-⊂
  ⊂-setoid Γ Δ .Setoid.isEquivalence .IsEquivalence.trans = trans-Eq-⊂

  trans-[] : ∀{Δ} (fs : [] ⊂ Δ) → Eq-⊂ (trans-⊂ [] fs) fs
  trans-[] []        = []
  trans-[] (wk a B fs) = wk a B (trans-[] fs)

  trans-refl : ∀{Γ Δ} (fs : Γ ⊂ Δ) → Eq-⊂ (trans-⊂ (refl-⊂ Γ) fs) fs
  trans-refl {[]}    fs        = trans-[] fs
  trans-refl {A ∷ Γ} (wk a B fs) = wk a B (trans-refl fs)
  trans-refl {A ∷ Γ} (f ∷ fs)  = (C .comp-id-r) ∷ (trans-refl fs)

  refl-trans : ∀{Γ Δ} (fs : Δ ⊂ Γ) → Eq-⊂ (trans-⊂ fs (refl-⊂ Γ)) fs
  refl-trans {[]}    fs        = refl-Eq-⊂ fs
  refl-trans {A ∷ Γ} (wk a B fs) = wk a B (refl-trans fs)
  refl-trans {A ∷ Γ} (f ∷ fs)  = (C .comp-id-l) ∷ (refl-trans fs)

  trans-assoc : ∀{Γ Δ Φ Ψ} (fs : Γ ⊂ Δ) (gs : Δ ⊂ Φ) (hs : Φ ⊂ Ψ)
              → Eq-⊂ (trans-⊂ fs (trans-⊂ gs hs)) (trans-⊂ (trans-⊂ fs gs) hs)
  trans-assoc fs          gs          (wk a C hs) = wk a C (trans-assoc fs gs hs)
  trans-assoc fs          (wk a B gs) (h ∷ hs)    = wk a _ (trans-assoc fs gs hs)
  trans-assoc (wk a A fs) (g ∷ gs)    (h ∷ hs)    = wk a _ (trans-assoc fs gs hs)
  trans-assoc (f ∷ fs)    (g ∷ gs)    (h ∷ hs)    = (C .comp-assoc) ∷ (trans-assoc fs gs hs)
  trans-assoc []          []          []          = []

  trans-cong : ∀{Γ Δ Φ} {fs fs' : Γ ⊂ Δ} {gs gs' : Δ ⊂ Φ}
             → Eq-⊂ fs fs'
             → Eq-⊂ gs gs'
             → Eq-⊂ (trans-⊂ fs gs) (trans-⊂ fs' gs')
  trans-cong e       (wk a B e') = wk a B (trans-cong e e')
  trans-cong (wk a A e) (_ ∷ e') = wk a _ (trans-cong e e')
  trans-cong (q ∷ e)   (q' ∷ e') = C .comp-cong q' q ∷ trans-cong e e'
  trans-cong []        []        = []

  LIST : Category o h e
  LIST .Obj                 = List (C .Obj)
  LIST .HomS                = ⊂-setoid
  LIST .id                  = refl-⊂
  LIST .comp gs fs          = trans-⊂ fs gs
  LIST .comp-id-l           = refl-trans _
  LIST .comp-id-r           = trans-refl _
  LIST .comp-assoc {f = fs} = trans-assoc _ _ fs
  LIST .comp-cong e e'      = trans-cong e' e

module Pointwise                = PointwiseAllowExtension ⊥
module OrderPreservingEmbedding = PointwiseAllowExtension ⊤

-- We can embed for instance a list morphism without weakning into one with weakening.

module Embedding {W W' : Set} (emb : W → W') {o h e} (C : Category o h e) where

  open module M  = PointwiseAllowExtension W C using (LIST; _⊂_) renaming (Eq-⊂ to _≈_)
  open module M' = PointwiseAllowExtension W' C using ()
    renaming (LIST to LIST'; _⊂_ to _⊂'_; Eq-⊂ to _≈'_)
  open PointwiseAllowExtension._⊂_
  open PointwiseAllowExtension.Eq-⊂

  cast : LIST .Obj → LIST' .Obj
  cast [] = []
  cast (x ∷ xs) = x ∷ cast xs

  cast-⊂ : ∀{xs ys} → xs M.⊂ ys → cast xs ⊂' cast ys
  cast-⊂ []          = []
  cast-⊂ (wk a B fs) = wk (emb a) B (cast-⊂ fs)
  cast-⊂ (f    ∷ fs) = f ∷ cast-⊂ fs

  cast-refl : ∀ xs → cast-⊂ (M.refl-⊂ xs) ≈' M'.refl-⊂ (cast xs)
  cast-refl []       = []
  cast-refl (x ∷ xs) = (C .reflEq) ∷ (cast-refl xs)

  cast-trans : ∀{xs ys zs} (fs : xs ⊂ ys) (gs : ys ⊂ zs)
             → cast-⊂ (M.trans-⊂ fs gs) ≈' M'.trans-⊂ (cast-⊂ fs) (cast-⊂ gs)

  cast-trans fs                [] = M'.refl-Eq-⊂ _
  cast-trans fs       (wk a B gs) = wk (emb a) B (cast-trans fs gs)
  cast-trans (wk a B fs) (g ∷ gs) = wk (emb a) _ (cast-trans fs gs)
  cast-trans (f ∷ fs)    (g ∷ gs) = C .reflEq ∷ cast-trans fs gs

  cast-cong : ∀{xs ys} {fs fs' : xs ⊂ ys} → fs ≈ fs' → cast-⊂ fs ≈' cast-⊂ fs'
  cast-cong []          = []
  cast-cong (e ∷ eq)    = e ∷ (cast-cong eq)
  cast-cong (wk a B eq) = wk (emb a) _ (cast-cong eq)

  Cast : Functor LIST LIST'
  Cast .App = cast
  Cast .map = cast-⊂
  Cast .map-id = cast-refl _
  Cast .map-comp {g = fs} = cast-trans fs _
  Cast .map-cong = cast-cong

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
