
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

-- Absurdity and Truth

data   ⊥ : Set where  -- empty type (no constructors)
record ⊤ : Set where  -- unit  type (no fields)

-- Equality, defined recursively

_≡_ : (x y : Nat) → Set
(zero  ≡ zero ) = ⊤
(suc x ≡ suc y) = (x ≡ y)
(_     ≡ _    ) = ⊥

-- Lemma: x ∸ x = 0

monus-diag : (x : Nat) → (monus x x ≡ zero)
monus-diag zero    = _
monus-diag (suc x) = monus-diag x

-- Some kind of Euclidean division

div : Nat → Nat → Nat
div zero    y = zero
div (suc x) y = {! suc (div (monus x y) y) !}
