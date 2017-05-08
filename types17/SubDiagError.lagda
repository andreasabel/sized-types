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
\end{code}
}

\newcommand{\apred}{\AgdaFunction{pred}}
\newcommand{\amonus}{\AgdaFunction{monus}}
\newcommand{\arefl}{\AgdaInductiveConstructor{refl}}
\newcommand{\azero}{\AgdaInductiveConstructor{zero}}
\newcommand{\asuc}{\AgdaInductiveConstructor{suc}}
\newcommand{\aNat}{\AgdaDatatype{Nat}}

\begin{code}
data Nat : Size → Set where
  zero  :  ∀ i → Nat (i + 1)
  suc   :  ∀ i → Nat i → Nat (i + 1)
\end{code}

We define subtraction $x \dotminus y$ on natural numbers, sometimes
called the $\amonus$ function, which computes $\max(0, x-y)$.  It is
defined by induction on the size $j$ of the second argument $y$, while
the output is bounded by size $i$ of the first argument $x$.  (The
input-output relation of $\amonus$ is needed for a natural
implementation of Euclidean divison.)

\begin{code}
monus : ∀ i → Nat i → ∀ j → Nat j → Nat i
monus i         x          .(j + 1) (zero j)   =  x
monus .(i + 1)  (zero i)   .(j + 1) (suc j y)  =  zero i
monus .(i + 1)  (suc i x)  .(j + 1) (suc j y)  =  monus i x j y
\end{code}

We wish to prove that subtracting $x$ from itself yields $0$, by
induction on $x$.  The case $x = 0$ should be trivial, as $x \dotminus
0 = x$ by definition, hence, $0 \dotminus 0 = 0$.  A simple proof by
reflexivity should suffice.  However, the goal shows a mismatch
between size $\infty$ and size $i$ coming from the computation of
$\amonus\,(i + 1)\,(\azero\,i)\,(i + 1)\,(\azero\,i)$.


\begin{code}
monus-diag : ∀ i → (x : Nat i) → zero ∞ ≡ monus i x i x
monus-diag .(i + 1) (zero i)   =  {! zero ∞ ≡ zero i !}  -- goal
monus-diag .(i + 1) (suc i x)  =  monus-diag i x
\end{code}

The proof could be completed by an application of reflexivity if Agda
ignored sizes where they act as \emph{type argument}, \ie, in
constructors and term-level function applications, but not in types
where they act as regular argument, \eg, in $\aNat\,i$.
