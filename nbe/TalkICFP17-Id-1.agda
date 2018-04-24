open import Agda.Builtin.Equality

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

pred : Nat → Nat
pred zero    = zero
pred (suc x) = x

-- Subtraction, tail-recursive, cutting off at zero.

monus : Nat → Nat → Nat
monus x zero    = x
monus x (suc y) = monus (pred x) y

-- Lemma: x ∸ x = 0

monus-diag : (x : Nat) → zero ≡ monus x x
monus-diag x = {!!}

-- Some kind of Euclidean division

div : Nat → Nat → Nat
div zero    y = zero
div (suc x) y = {! suc (div (monus x y) y) !}
