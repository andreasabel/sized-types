-- Andreas Abel, Andrea Vezzosi, Theo Winterhalter
-- Normalization by Evaluation for Sized Dependent Types
-- EPFL, 14 September 2017

{-# OPTIONS --experimental-irrelevance #-}
{-# OPTIONS --show-irrelevant #-}

open import Agda.Builtin.Size renaming (ω to ∞)

data Nat : ..(i : Size) → Set where
  zero : ∀ .i → Nat (↑ i)
  suc  : ∀ .i → Nat i → Nat (↑ i)

pred : ∀ .i → Nat i → Nat i
pred _ (zero _ ) = zero _
pred _ (suc _ x) = x

-- Subtraction, tail-recursive, cutting off at zero _
-- E.g.  5 ∸ 3 = 2;   3 ∸ 5 = 0

monus : ∀ .i .j → Nat i → Nat j → Nat i
monus _ _ x (zero _ ) = x
monus _ _ x (suc _ y) = monus _ _ (pred _ x) y

-- Absurdity and Truth

data   ⊥ : Set where  -- empty type (no constructors)
record ⊤ : Set where  -- unit  type (no fields)

-- Equality, defined recursively

Eq : ∀ .i (x y : Nat i) → Set
Eq _ (zero _ ) (zero _ ) = ⊤
Eq _ (suc _ x) (suc _ y) = Eq _ x y
Eq _ _       _       = ⊥

-- Lemma: x ∸ x = 0

monus-diag : ∀ .i (x : Nat i) → Eq ∞ (monus i i x x) (zero _)
monus-diag .(↑ i) (zero i) = _
monus-diag .(↑ i) (suc i x) = monus-diag i x

-- Some kind of Euclidean division

div : ∀ .i → Nat i → Nat ∞ → Nat i
div _      (zero _ ) y = zero _
div .(↑ i) (suc i x) y = suc _ (div i (monus i _ x y) y)
