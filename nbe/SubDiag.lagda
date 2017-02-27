The solution we present in this article already works in current Agda,\footnote{%
\url{https://github.com/agda/agda}, development version of 2017-02-27.}
but the implementation is not perfect.  It has to be switched on by a flag explicitly:

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

prove_by_ : (A : Set) → A → A
prove A by x = x
\end{code}
}

We mark the size argument of $\aNat$ as \emph{shape irrelevant} by preceding the binder with two dots.  In a future implementation, we could treat all data type parameters as shape irrelevant by default.
In the types of the constructors, we mark argument $i$ as \emph{irrelevant} by prefixing the binder with a single dot.  This is sound because $i$ occurs in subsequent parts of the type only in shape-irrelevant positions.

\begin{code}
data Nat : ..(i : Size) → Set where
  zero  :  ∀ .i → Nat (i + 1)
  suc   :  ∀ .i → Nat i → Nat (i + 1)
\end{code}

Similarly, ``type'' argument $i$ to $\apred$ is irrelevant.  Agda checks that it only occurs shape-irrelevantly in the type and irrelevantly in the term.  It succeeds since $i$ is also an irrelevant argument to the constructors $\azero$ and $\asuc$; otherwise, we would get a type error.

\begin{code}
pred : ∀ .i → Nat i → Nat i
pred .(i + 1) (zero i)   =  zero i
pred .(i + 1) (suc i x)  =  x
\end{code}

The two size arguments $i$ and $j$ to $\amonus$ are also irrelevant.  In this case, we succeed since the size argument to $\apred$ has been declared irrelevant.

\begin{code}
monus : ∀ .i → Nat i → ∀ .j → Nat j → Nat i
monus i x .(j + 1) (zero j)   =  x
monus i x .(j + 1) (suc j y)  =  monus i (pred i x) j y
\end{code}

Now, with sizes being ignored in the involved terms, we can complete the proof of our lemma:

\begin{code}
monus-diag : ∀ .i → (x : Nat i) → zero ∞ ≡ monus i x i x
monus-diag .(i + 1) (zero i)   =  prove zero ∞ ≡ zero i               by refl
monus-diag .(i + 1) (suc i x)  =  prove zero ∞ ≡ monus (i + 1) x i x  by monus-diag i x
\end{code}
