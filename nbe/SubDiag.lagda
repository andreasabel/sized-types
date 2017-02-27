\begin{code}
{-# OPTIONS --experimental-irrelevance #-}
\end{code}

\AgdaHide{
\begin{code}
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
\end{code}
}

\begin{code}
data Nat : ..(i : Size) → Set where
  zero : ∀ .i → Nat (↑ i)
  suc  : ∀ .i → Nat i → Nat (↑ i)
\end{code}

\begin{code}
pred : .(i : Size) → Nat i → Nat i
pred .(↑ i) (zero i)  = zero i
pred .(↑ i) (suc i x) = x
\end{code}

\begin{code}
monus : .(i : Size) → Nat i → .(j : Size) → Nat j → Nat i
monus i x .(↑ j) (zero j)  = x
monus i x .(↑ j) (suc j y) = monus i (pred i x) j y
\end{code}

\begin{code}
monus-diag : .(i : Size) (x : Nat i) → zero ∞ ≡ monus i x i x
monus-diag .(↑ i) (zero i)  = refl
monus-diag .(↑ i) (suc i x) = monus-diag i x
\end{code}
