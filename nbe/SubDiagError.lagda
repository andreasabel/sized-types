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
\newcommand{\azero}{\AgdaInductiveConstructor{zero}}
\newcommand{\asuc}{\AgdaInductiveConstructor{suc}}
\newcommand{\aNat}{\AgdaDatatype{Nat}}

The problem of the current implementation of sized types in Agda can be demonstrated by a short example.  Consider the type of sized natural numbers.

\begin{code}
data Nat : Size → Set where
  zero  :  ∀ i → Nat (i + 1)
  suc   :  ∀ i → Nat i → Nat (i + 1)
\end{code}

The predecessor function is \emph{size preserving}, \ie, the output can be assigned the same upper bound $i$ as the input.

\begin{code}
pred : ∀ i → Nat i → Nat i
pred .(i + 1) (zero i)   =  zero i
pred .(i + 1) (suc i x)  =  x
\end{code}
Note that in the second clause, we have applied subtyping to cast $x : \aNat\,i$ to $\aNat\,(i + 1)$.
The dot on the left hand side, preceding $(i + 1)$, marks an \emph{inaccessible} pattern.  Its value is determined by the subsequent match on the natural number argument, no actual matching has to be carried out on this argument.

We now define subtraction $x \dotminus y$ on natural numbers, sometimes called the \emph{monus} function, which computes $\max(0, x-y)$.  It is defined by induction on the size $j$ of the second argument $y$, while the output is bounded by size $i$ of the first argument $x$.  There are several ways to implement it, we have chosen the tail-recursive variant which treats the first argument as accumulator.  It computes the result by applying the predecessor function $y$-times to $x$.

\begin{code}
monus : ∀ i → Nat i → ∀ j → Nat j → Nat i
monus i x .(j + 1) (zero j)   =  x
monus i x .(j + 1) (suc j y)  =  monus i (pred i x) j y
\end{code}

To document subgoals in proof terms, we introduce a mixfix version of the identity function with a visible type argument:

\begin{code}
prove_by_ : (A : Set) → A → A
prove A by x = x
\end{code}

We now wish to prove that subtracting $x$ from itself yields $0$, by induction on $x$.  The case $x = 0$ should be trivial, as $x \dotminus 0 = x$ by definition, hence, $0 \dotminus 0 = 0$.  As simple proof by reflexivity should suffice.  In case $x + 1$, the goal $0 \equiv (x + 1) \dotminus (x + 1)$ should reduce to $0 \equiv x \dotminus x$, thus, an application of the induction hypothesis should suffice.

\begin{code}
monus-diag : ∀ i → (x : Nat i) → zero ∞ ≡ monus i x i x
monus-diag .(i + 1) (zero i)   =  prove zero ∞ ≡ zero i               by {! refl !}
monus-diag .(i + 1) (suc i x)  =  prove zero ∞ ≡ monus (i + 1) x i x  by {! monus-diag i x !}
\end{code}

Unfortunately, in Agda our proof does not go through, as sizes get in the way.
In the first goal, there is a mismatch between size $\infty$ and size $i$ coming from the computation of $\amonus\,(i + 1)\,(\azero\,i)\,(i + 1)\,(\azero\,i)$.  In the first goal, there is a mismatch betwenn size $i + 1$ in term $\amonus\,(i + 1)\,x\,i\,x$ of the reduced goal and size $i$ of the respective term $\amonus\,i\,x\,i\,x$ from the induction hypothesis we wish to apply.

The proof would go through if Agda ignored sized where they act as \emph{type argument}, \ie, in constructors and term-level function applications, but not in types where they act as regular argument, \eg, in $\aNat\,i$.
