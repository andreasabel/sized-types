{-# OPTIONS --experimental-irrelevance #-}
{-# OPTIONS -v term:20 #-}

open import Agda.Primitive
  public using (lzero; lsuc)

open import Agda.Builtin.Size
  public using (Size; Size<_; ↑_) renaming (ω to oo)

open import Agda.Builtin.Nat
  public using (suc) renaming (Nat to ℕ)

_+_ : Size → ℕ → Size
s + 0 = s
s + suc n = ↑ (s + n)

data Nat ..(i : Size) : Set where
  zero : Nat (i)
  suc  : ∀ .(j : Size< i) → Nat j → Nat i

caseof : ∀{a b} {A : Set a} (B : A → Set b) → (x : A) → ((x : A) → B x) → B x
caseof B x f = f x

syntax caseof B x f = case x return B of f

fix : ∀{ℓ}
  (T : ..(i : Size) → Nat i → Set ℓ)
  (f : ∀ .j → (∀ .(k : Size< j) → (x : Nat k) → T k x) → (x : Nat j) → T j x)
  .i
  (x : Nat i)
  → T i x
fix T f i (zero)    = {!!} -- f i (fix T f) (zero)
fix T f i (suc j n) = f i {!rec!} (suc j n)
  where
  rec : ∀ .(k : Size< i) → (x : Nat k) → T k x
  rec k zero = fix T f k zero -- k is not usable
  rec k (suc l x) = fix T f k (suc l x)
