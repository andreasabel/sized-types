\AgdaHide{
\begin{code}
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

prove_by_ : (A : Set) → A → A
prove A by x = x

-- syntax prove A by a = a ∈ A

id : (A : Set) → A → A
id A x = x

infix 0 id
syntax id A a = a ∈ A
\end{code}
}
\newcommand{\aNat}{
\begin{code}
data Nat : (i : Size) → Set where
  zero  :  ∀ i → Nat (i + 1)
  suc   :  ∀ i → Nat i → Nat (i + 1)
\end{code}
}
\newcommand{\aPredTy}{
\begin{code}
pred : ∀ i → Nat i → Nat i
\end{code}
}
\newcommand{\aPredImpl}{
\begin{code}
pred .(i + 1) (zero i)   =  zero i
pred .(i + 1) (suc i x)  =  x
\end{code}
}
\newcommand{\aMonus}{
\begin{code}
monus : ∀ i (x : Nat i) j (y : Nat j) → Nat i
monus i x .(j + 1) (zero j)   =  x
monus i x .(j + 1) (suc j y)  =  monus i (pred i x) j y

monus-diag : ∀ i → (x : Nat i) → zero ∞ ≡ monus i x i x
monus-diag .(i + 1) (zero i)   =  {!!} ∈ zero ∞ ≡ zero i
monus-diag .(i + 1) (suc i x)  =  {!!} ∈ zero ∞ ≡ monus (i + 1) x i x
\end{code}
}
