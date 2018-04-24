open import Agda.Builtin.Size renaming (ω to ∞)
open import Agda.Builtin.Equality

data Nat : Size → Set where
  zero : ∀ i → Nat (↑ i)
  suc  : ∀ i → Nat i → Nat (↑ i)

pred : ∀ i → Nat i → Nat i
pred _ (zero i)  = zero i
pred _ (suc i x) = x

-- Subtraction, tail-recursive, cutting off at zero.

monus : ∀ i j → Nat i → Nat j → Nat i
monus i _ x (zero j)  = x
monus i _ x (suc j y) = monus i _ (pred i x) y

-- Lemma: x ∸ x = 0

monus-diag : ∀ i (x : Nat i) → (monus i i x x) (zero ∞)
monus-diag .(↑ i) (zero i)  = {!refl!}
monus-diag .(↑ i) (suc i x) = {!!}

-- Some kind of Euclidean division

div : ∀ i → Nat i → Nat ∞ → Nat i
div .(↑ i) (zero i)  y = zero i
div .(↑ i) (suc i x) y = suc _ (div i (monus i _ x y) y)
