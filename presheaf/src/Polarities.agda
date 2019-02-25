{-# OPTIONS --postfix-projections #-}

module Polarities where

open import Library
open import Category
open import Category.List

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

Pol = POL .Obj

-- Polarities, pretty names

pattern ± = true  , true
pattern + = true  , false
pattern - = false , true
pattern ∅ = false , false

-- Size contexts

open OrderPreservingEmbedding using () renaming (LIST to OPE)
open Pointwise                using (LIST)

-- Category of size contexts

SCXT = OPE POL
SCxt = SCXT .Obj

-- Forget : OPE

-- Selections

-- data Sel : SCxt → Set where
--   []   : Sel []
--   _∷_  : ∀ {p q : Pol} {Δ} (le : {!!}) (δ : Sel Δ) → Sel (q ∷ Δ)
