{-# OPTIONS --experimental-irrelevance #-}

open import Base

data Hungry (A : Set) : ..(i : Size) → Set where
  inn : ∀.{i} → (f : A → Hungry A i) → Hungry A (i + 1)

out : ∀.{i}{A} → Hungry A (i + 1) → A → Hungry A i
out (inn f) = f

postulate
  pred : ∀.{i} → Nat (i + 1) → Nat i

s : ∀.{i j} → Hungry (Nat j) i → Hungry (Nat (j + 1)) i
s (inn f) = inn λ n → s (f (pred n))

p : ∀.{i j} → Hungry (Nat (j + 1)) i → Hungry (Nat j) i
p (inn f) = inn λ n → p (f (suc _ n))

h : ∀.{i} → Nat i → Hungry (Nat i) i
h (zero _)  = inn λ n → s (h (pred n))
h (suc _ _) = inn λ n → s (h (pred n))

tr : ∀.{i}{A : Set} → Hungry (Nat oo) i → A
tr (inn f) = tr (p (f (suc _ (zero _))))

loop : ∀{A : Set} → A
loop = tr (h (zero _))
