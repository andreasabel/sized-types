{-# OPTIONS --experimental-irrelevance #-}
{-# OPTIONS --show-irrelevant #-}

open import Agda.Builtin.Size
  public using (Size; ↑_) renaming (ω to ∞)

open import Agda.Builtin.Nat
  public using (suc) renaming (Nat to ℕ)

open import Agda.Builtin.Equality

_+_ : Size → ℕ → Size
s + 0 = s
s + suc n = ↑ (s + n)

-- Sized natural numbers

data Nat : ..(i : Size) → Set where
  zero : ∀ .i → Nat (↑ i)
  suc  : ∀ .i → Nat i → Nat (↑ i)

-- Predecessor preserves upper bound

pred : .(i : Size) → Nat i → Nat i
pred .(↑ i) (zero i)  = zero i
pred .(↑ i) (suc i x) = x

-- Subtraction  sub x y = y ∸ x  preserves upper bound

sub : .(j : Size) → Nat j → .(i : Size) → Nat i → Nat i
sub .(↑ j) (zero j)  i y = y
sub .(↑ j) (suc j x) i y = sub j x i (pred i y)

-- x ∸ x ≡ 0

sub-diag : .(i : Size) (x : Nat i) → _≡_ {A = Nat ∞} (sub i x i x) (zero ∞)
sub-diag .(↑ i) (zero i)  = refl
sub-diag .(↑ i) (suc i x) = sub-diag i x
