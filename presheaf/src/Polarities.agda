{-# OPTIONS --postfix-projections #-}

module Polarities where

open import Library
open import Category

-- The category  false ≤ true : Bool

BOOL : Category lzero lzero lzero
BOOL .Obj = Bool
BOOL .HomS a b .Setoid.Carrier = a Bool.≤ b
BOOL .HomS a b .Setoid._≈_ _ _ = ⊤
BOOL .HomS a b .Setoid.isEquivalence = _
BOOL .id b       = Bool.refl-≤
BOOL .comp p q   = Bool.trans-≤ q p
BOOL .comp-id-l  = _
BOOL .comp-id-r  = _
BOOL .comp-assoc = _
BOOL .comp-cong  = _

-- POL = BOOL × BOOL

POL : Category lzero lzero lzero
POL = BOOL ×-cat BOOL

-- Polarities, pretty names

pattern ± = true  , true
pattern + = true  , false
pattern - = false , true
pattern ∅ = false , false

-- Size contexts

module OrderPreservingEmbedding {o h e} (C : Category o h e) where

  EObj = List (C .Obj)

  data _⊂_ : (Γ Δ : EObj) → Set h where
    []   : [] ⊂ []
    wk   : ∀{Γ Δ}     (B : C .Obj)     (fs : Γ ⊂ Δ) → Γ       ⊂ (B ∷ Δ)
    _∷_  : ∀{A B Γ Δ} (f : C .Hom A B) (fs : Γ ⊂ Δ) → (A ∷ Γ) ⊂ (B ∷ Δ)

  refl-⊂ : ∀ Γ → Γ ⊂ Γ
  refl-⊂ []      = []
  refl-⊂ (A ∷ Γ) = C .id A ∷ refl-⊂ Γ

  trans-⊂ : ∀{Γ Δ Φ} → Γ ⊂ Δ → Δ ⊂ Φ → Γ ⊂ Φ
  trans-⊂ fs        []       = fs
  trans-⊂ fs       (wk B gs) = wk B (trans-⊂ fs gs)
  trans-⊂ (wk A fs) (g ∷ gs) = wk _ (trans-⊂ fs gs)
  trans-⊂ (f  ∷ fs) (g ∷ gs) = C .comp g f ∷ (trans-⊂ fs gs)

  -- ⊂-Eq : ∀{Γ Δ} (fs gs : Γ ⊂ Δ) → Set {!!}
  -- ⊂-Eq [] [] = Lift _ ⊤
  -- ⊂-Eq (wk B fs) (wk .B gs) = ⊂-Eq fs gs
  -- ⊂-Eq (wk B fs) (f ∷ gs) = {!!}
  -- ⊂-Eq (f ∷ fs) (wk B gs) = {!Lift _ ⊥!}
  -- ⊂-Eq (f ∷ fs) (g ∷ gs) = C .Eq f g × ⊂-Eq fs gs

  data Eq-⊂ : ∀{Γ Δ} (fs gs : Γ ⊂ Δ) → Set e where
    []  : Eq-⊂ [] []
    _∷_ : ∀{A B Γ Δ} {f g : C .Hom A B} {fs gs : Γ ⊂ Δ}
        → C .Eq f g → Eq-⊂ fs gs → Eq-⊂ (f ∷ fs) (g ∷ gs)
    wk  : ∀ B {Γ Δ}  {fs gs : Γ ⊂ Δ}
        → Eq-⊂ fs gs → Eq-⊂ (wk B fs) (wk B gs)

  refl-Eq-⊂ : ∀{Γ Δ} (fs : Γ ⊂ Δ) → Eq-⊂ fs fs
  refl-Eq-⊂ []        = []
  refl-Eq-⊂ (wk B fs) = wk B (refl-Eq-⊂ fs)
  refl-Eq-⊂ (f ∷ fs)  = C .reflEq ∷ refl-Eq-⊂ fs

  sym-Eq-⊂ : ∀{Γ Δ} {fs gs : Γ ⊂ Δ} → Eq-⊂ fs gs → Eq-⊂ gs fs
  sym-Eq-⊂ []       = []
  sym-Eq-⊂ (e ∷ p)  = C .symEq e ∷ sym-Eq-⊂ p
  sym-Eq-⊂ (wk B p) = wk B (sym-Eq-⊂ p)

  trans-Eq-⊂ : ∀{Γ Δ} {fs gs hs : Γ ⊂ Δ}
             → Eq-⊂ fs gs → Eq-⊂ gs hs → Eq-⊂ fs hs
  trans-Eq-⊂ []       []         = []
  trans-Eq-⊂ (e ∷ p)  (e' ∷ p')  = C .transEq e e' ∷ trans-Eq-⊂ p p'
  trans-Eq-⊂ (wk B p) (wk .B p') = wk B (trans-Eq-⊂ p p')

  ⊂-setoid : (Γ Δ : EObj) → Setoid h e
  ⊂-setoid Γ Δ .Setoid.Carrier = Γ ⊂ Δ
  ⊂-setoid Γ Δ .Setoid._≈_ fs gs = Eq-⊂ fs gs
  ⊂-setoid Γ Δ .Setoid.isEquivalence .IsEquivalence.refl  = refl-Eq-⊂ _
  ⊂-setoid Γ Δ .Setoid.isEquivalence .IsEquivalence.sym   = sym-Eq-⊂
  ⊂-setoid Γ Δ .Setoid.isEquivalence .IsEquivalence.trans = trans-Eq-⊂

  trans-[] : ∀{Δ} (fs : [] ⊂ Δ) → Eq-⊂ (trans-⊂ [] fs) fs
  trans-[] []        = []
  trans-[] (wk B fs) = wk B (trans-[] fs)

  trans-refl : ∀{Γ Δ} (fs : Γ ⊂ Δ) → Eq-⊂ (trans-⊂ (refl-⊂ Γ) fs) fs
  trans-refl {[]}    fs        = trans-[] fs
  trans-refl {A ∷ Γ} (wk B fs) = wk B (trans-refl fs)
  trans-refl {A ∷ Γ} (f ∷ fs)  = (C .comp-id-r) ∷ (trans-refl fs)

  refl-trans : ∀{Γ Δ} (fs : Δ ⊂ Γ) → Eq-⊂ (trans-⊂ fs (refl-⊂ Γ)) fs
  refl-trans {[]}    fs        = refl-Eq-⊂ fs
  refl-trans {A ∷ Γ} (wk B fs) = wk B (refl-trans fs)
  refl-trans {A ∷ Γ} (f ∷ fs)  = (C .comp-id-l) ∷ (refl-trans fs)

  trans-assoc : ∀{Γ Δ Φ Ψ} (fs : Γ ⊂ Δ) (gs : Δ ⊂ Φ) (hs : Φ ⊂ Ψ)
              → Eq-⊂ (trans-⊂ fs (trans-⊂ gs hs)) (trans-⊂ (trans-⊂ fs gs) hs)
  trans-assoc fs        gs        (wk C hs) = wk C (trans-assoc fs gs hs)
  trans-assoc fs        (wk B gs) (h ∷ hs)  = wk _ (trans-assoc fs gs hs)
  trans-assoc (wk A fs) (g ∷ gs)  (h ∷ hs)  = wk _ (trans-assoc fs gs hs)
  trans-assoc (f ∷ fs)  (g ∷ gs)  (h ∷ hs)  = (C .comp-assoc) ∷ (trans-assoc fs gs hs)
  trans-assoc []        []        []        = []

  trans-cong : ∀{Γ Δ Φ} {fs fs' : Γ ⊂ Δ} {gs gs' : Δ ⊂ Φ}
             → Eq-⊂ fs fs'
             → Eq-⊂ gs gs'
             → Eq-⊂ (trans-⊂ fs gs) (trans-⊂ fs' gs')
  trans-cong e       (wk B e') = wk B (trans-cong e e')
  trans-cong (wk A e) (_ ∷ e') = wk _ (trans-cong e e')
  trans-cong (q ∷ e) (q' ∷ e') = C .comp-cong q' q ∷ trans-cong e e'
  trans-cong []      []        = []

  OPE : Category o h e
  OPE .Obj                 = EObj
  OPE .HomS                = ⊂-setoid
  OPE .id                  = refl-⊂
  OPE .comp gs fs          = trans-⊂ fs gs
  OPE .comp-id-l           = refl-trans _
  OPE .comp-id-r           = trans-refl _
  OPE .comp-assoc {f = fs} = trans-assoc _ _ fs
  OPE .comp-cong e e'      = trans-cong e' e

open OrderPreservingEmbedding using (OPE)

-- Category of size contexts

SCXT = OPE POL
