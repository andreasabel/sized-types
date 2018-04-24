{-# OPTIONS --experimental-irrelevance #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --show-irrelevant #-}

open import Agda.Builtin.Size
  public using (Size) renaming (ω to ∞; ↑_ to _+1)

open import Agda.Builtin.Nat
  public using (suc) renaming (Nat to ℕ)

open import Agda.Builtin.Equality

_+_ : Size → ℕ → Size
s + 0 = s
s + suc n = (s + n) +1

-- Sized natural numbers.

data Nat : (i : Size) → Set where
  zero  :  ∀ i → Nat (i + 1)
  suc   :  ∀ i → Nat i → Nat (i + 1)

-- Predecessor (size-preserving).

pred : ∀ i → Nat i → Nat i
pred .(i + 1) (zero i)   =  zero i
pred .(i + 1) (suc i x)  =  x

-- Cut-off minus (size-preserving)

monus : ∀ i (x : Nat i) j (y : Nat j) → Nat i
monus = {!!}

monus-diag : ∀ i → (x : Nat i) → zero ∞ ≡ monus i x i x
monus-diag = {!!}
