{-# OPTIONS --experimental-irrelevance #-}

open import Agda.Primitive
  public using (lzero; lsuc)

open import Agda.Builtin.Size
  public using (Size; ↑_) renaming (ω to oo)

open import Agda.Builtin.Nat
  public using (suc) renaming (Nat to ℕ)

_+_ : Size → ℕ → Size
s + 0 = s
s + suc n = ↑ (s + n)

data Nat : ..(i : Size) → Set where
  zero : ∀.{i} → Nat (↑ i)
  suc  : ∀.{i} → Nat i → Nat (↑ i)


caseof : ∀{a b} {A : Set a} (B : A → Set b) → (x : A) → ((x : A) → B x) → B x
caseof B x f = f x

syntax caseof B x f = case x return B of f

fix : ∀{ℓ}
  (T : ..(i : Size) → Nat i → Set ℓ)
  (f : ∀.{i} → ((x : Nat i) → T i x) → (x : Nat (↑ i)) → T (↑ i) x)
  .{i}
  (x : Nat i)
  → T i x
fix T f zero    = f (fix T f) zero
fix T f (suc n) = f (fix T f) (suc n)
