-- Andreas Abel, Andrea Vezzosi, Theo Winterhalter
-- Normalization by Evaluation for Sized Dependent Types [paper #33]
-- ICFP, 6 September 2017

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

pred : Nat → Nat
pred zero    = zero
pred (suc x) = x

-- Subtraction, tail-recursive, cutting off at zero
-- E.g.  5 ∸ 3 = 2;   3 ∸ 5 = 0

monus : Nat → Nat → Nat
monus x zero    = x
monus x (suc y) = monus (pred x) y

-- Absurdity and Truth

data   ⊥ : Set where  -- empty type (no constructors)
record ⊤ : Set where  -- unit  type (no fields)

-- Equality, defined recursively

Eq : (x y : Nat) → Set
Eq zero    zero    = ⊤
Eq (suc x) (suc y) = Eq x y
Eq _       _       = ⊥

-- Lemma: x ∸ x = 0

monus-diag : (x : Nat) → Eq (monus x x) zero
monus-diag zero    = _
monus-diag (suc x) = monus-diag x

-- Some kind of Euclidean division

div : Nat → Nat → Nat
div zero    y = zero
div (suc x) y = {! suc (div (monus x y) y) !}
