-- Andreas Abel, Andrea Vezzosi, Theo Winterhalter
-- Normalization by Evaluation for Sized Dependent Types [paper #33]
-- ICFP, 6 September 2017

open import Agda.Builtin.Size renaming (ω to ∞)

data Nat : Size → Set where
  zero : ∀ i → Nat (↑ i)
  suc  : ∀ i → Nat i → Nat (↑ i)

pred : ∀ i → Nat i → Nat i
pred _ (zero i)  = zero i
pred _ (suc i x) = x

-- Subtraction, tail-recursive, cutting off at zero
-- E.g.  5 ∸ 3 = 2;   3 ∸ 5 = 0

monus : ∀ i j → Nat i → Nat j → Nat i
monus i _ x (zero j)  = x
monus i _ x (suc j y) = monus i _ (pred i x) y

-- Absurdity and Truth

data   ⊥ : Set where  -- empty type (no constructors)
record ⊤ : Set where  -- unit  type (no fields)

-- Equality, defined recursively

Eq : ∀ i (x y : Nat i) → Set
Eq _ (zero _)  (zero _)  = ⊤
Eq _ (suc _ x) (suc _ y) = Eq _ x y
Eq _ _         _         = ⊥

-- Lemma: x ∸ x = 0

monus-diag : ∀ i (x : Nat i) → Eq ∞ (monus i i x x) (zero ∞)
monus-diag i x = {!x!}

-- Some kind of Euclidean division

div : ∀ i → Nat i → Nat ∞ → Nat i
div .(↑ i) (zero i)  y = zero i
div .(↑ i) (suc i x) y = suc _ (div i (monus i _ x y) y)
