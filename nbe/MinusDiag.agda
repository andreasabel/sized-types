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

data Nat : ..(i : Size) → Set where
  zero  :  ∀ .i → Nat (i + 1)
  suc   :  ∀ .i → Nat i → Nat (i + 1)

pred : ∀ .i → Nat i → Nat i
pred .(i + 1) (zero i)   =  zero i
pred .(i + 1) (suc i x)  =  x

monus : ∀ .i → Nat i → ∀ .j → Nat j → Nat i
monus i x .(j + 1) (zero j)   =  x
monus i x .(j + 1) (suc j y)  =  monus i (pred i x) j y

prove_by_ : (A : Set) → A → A
prove A by x = x

monus-diag : ∀ .i → (x : Nat i) → zero ∞ ≡ monus i x i x
monus-diag .(i + 1) (zero i)   =  prove zero ∞ ≡ zero i               by {! refl !}
monus-diag .(i + 1) (suc i x)  =  prove zero ∞ ≡ monus (i + 1) x i x  by {! monus-diag i x !}
