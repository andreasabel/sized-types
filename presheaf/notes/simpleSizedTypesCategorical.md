Categorical models of sized types
=================================

With intrinsic sized typing, such as in categorical models of sized
types or well-typed syntax involving types, there is no simple
argument for size irrelevance, such as we can get for type assignment.
By size irrelevance we mean that computation does not depend on sizes,
they only justify well-definedness.

In the type-assignment approach we start with a programs that are not
guaranteed to terminate, like untyped lambda terms, simply-typed
lambda terms with general recursion, or a domain-theoretic model.

The type-assignment approach does not work so well for dependent
types, since we need to restrict the terms appearing in dependent
types to be total.  Otherwise, it is hard to define the semantics of
types; one would need to clarify what the semantics of a
non-terminating type should be, and there could be two
interpretations: A non-terminating type contains all values, or no
values.  The first interpretation ("negative") is a coinductive
interpretation of the judgemental equality, the second ("positive") an
inductive interpretation... (end of digression).


# Terms as natural transformations

The typing judgement

    t : Δ; Γ ⊢ A

states that t is a term of type A in context Γ, where Γ and A can
mention size variables declared in Δ.  The typing rules ensure that t
computationally only depends on the variables in Γ, but not on the
size variables in Δ.

Semantically, this size irrelevance could be established by size
parametricity, i.e., we would like to obtain for all size valuations
σ,σ' ∈ ⟦Δ⟧,

    ⦅t⦆σ  ⟦Γ ⊢ A⟧(σ,σ') ⦅t⦆σ'

for a suitable relational interpretation ⟦Γ ⊢ A⟧ of sequents Γ ⊢ A.
However, it is not clear how this interpretation would look like, as
there is no obvious way how to relate values u : Aσ and u' : Aσ' for
sizes σ,σ' whose relations we do not know (even if Γ is empty).

For our purposes, naturality (instead of full parametricity) may be
enough, since we can exploit the ordering _≤_ on ordinals to build
mappings between Aσ and Aσ' to transport u and u' to a common type
where they can be compared.

Thus, we may interpret Γ ⊢ A as a set (category?) of natural
transformations

    ⦅t⦆ : (σ ∈ ⟦Δ⟧) → ⟦Γ⟧σ → ⟦A⟧σ
    with ⟦A⟧(σ ≤ σ') ∘ ⦅t⦆σ = ⦅t⦆σ' ∘ ⟦Γ⟧(σ ≤ σ')

In particular, if we have a computation of a sized natural number

    t : Δ; ⊢ Nˢ

we get with v = ⦅t⦆

    ℕ(sσ ≤ sσ') vσ = vσ'

and, via embedding ("erasure") into the limit ℕ∞, which is just the
natural numbers,

    erN(α) : ℕ(α) → ℕ

    erN(sσ) vσ = erN(sσ') vσ'

which proves that the computed number does not depend on the choice of
size valuation σ.

Here ℕ(∙) is the presheaf O → Set with N(α) = {n : N | n ≤ α}.
O is the strict preorder on ordinals, i.e., we have

    _<_, _≤_ : O → O → Prop

with _<_ ⊆ _≤_ and _<_ well-founded.


# The mixed-variance problem

A priori, not all sized types are monotone, e.g. the type

    Nⁱ → Nⁱ

is mixed-variant in size i, and also, we want antitone types like

    Sⁱ

the type of streams of definedness depth ≥ i.  While the usual monotonization

    ∀j≥i. Nʲ → Nʲ

used for the presheaf exponential could maybe work for function types,
it does not make sense for streams, since

    ∀j≥i. Sʲ

is already the type of fully defined streams.

## Profunctors

A way of incorporating types of different size variance is to switch to profuctors

    F : Oᵒᵖ × O → Set

which accomodates co-, contra-, and mixed variant sized types (and, of
course, non-sized types).

    B, N, S, N→N : Oᵒᵖ × O → Set

        B(α,β) = 𝔹             -- Booleans
        N(α,β) = ℕ(β)          -- Sized natural numbers
        S(α,β) = 𝕊(α)           -- Sized streams
    (N→N)(α,β) = ℕ(α) → ℕ(β)   -- Size-preserving functions

On such profunctors we can define a function space

    A ⇒ B : Oᵒᵖ × O → Set
    A ⇒ B = A⁻ → B
    (A → B)(α,β) = A(β,α) → B(α,β)

which is the pointwise function space plus flipping the domain

    (∙)⁻ : (Oᵒᵖ × O → Set) → O × Oᵒᵖ → Set.

(It is not clear whether we need this function space, at least to
model lambda calculus we need the usual presheaf exponential instead.)

If we work with such profunctors, the "officially" all types are
mixed-variant, but "internally", they might be co- or contra-variant;
however, their behavior is not statically exposed.

With regards to nomenclature, our profunctors are just presheaves on category

    O₂ = O × Oᵒᵖ

## Wellfoundedness

We can extend strict ordering on O to O₂ by setting

    (α,β) < (α',β')  iff  α < α'  and  β = β'

which is wellfounded.  This should allow us to justify well-founded
recursion on sizes

    fix : (∀i. (∀j<i. Aʲ) → Aⁱ) → ∀i. Aⁱ


# Interpretation of the judgements

In the typing judgement

    t : Δ; Γ ⊢ A

Δ is just a natural number, the number of size variables.  We interpret it as

    ⟦0⟧   = 1        (the one-point preorder, i.e., unit category)
    ⟦Δ+1⟧ = ⟦Δ⟧ × O₂ (the simultaneous product of preorders, i.e., product of categories)

The term t is interpreted as a morphism in the category PSh⟦Δ⟧ of

    objects Γ,A,B: presheaves over ⟦Δ⟧
    morphisms    : natural transformations A → B

Weakening of types Δ ⊢ A to Δ,i ⊢ A is

    Wk₁ : PSh⟦Δ⟧ → PSh⟦Δ+1⟧
    Wk₁(A)(σ,(α,β)) = A(σ)

thus, it is just _ ∘ π₁ with π₁ being the left projection out of a product category.

Weakening of terms by a new size variable is

       Δ; Γ ⊢ A
    wk₁ ----------------
       Δ+1; Wk₁ Γ ⊢ Wk₁ A

    wk₁ : PSh⟦Δ⟧(Γ,A) → PSh⟦Δ+1⟧(Wk₁ Γ, Wk₁ A)
    wk₁ t (σ,_) = t σ

which is also just _ ∘ π₁.

More generally, if we have projection ⟦τ⟧ : ⟦Δ'⟧ → ⟦Δ⟧ for an
order-preserving embedding τ : Δ ≤ Δ', we can weaken types and terms
as follows:

    Wk τ : PSh⟦Δ⟧ → PSh⟦Δ'⟧
    Wk τ A = A ∘ ⟦τ⟧

    wk τ : PSh⟦Δ⟧(Γ,A) → PSh⟦Δ'⟧(Wk τ Γ, Wk τ A)
    wk τ t = t ∘ ⟦τ⟧

Term variables (de Bruijn indices) x are interpreted as projections ⟦x⟧ : PSh⟦Δ⟧(Γ,A)

    ⟦0⟧  σ(γ,a) = a
    ⟦x+1⟧σ(γ,a) = ⟦x⟧σγ

Thus ⟦x⟧σ = π₂ ∘ π₁ˣ.

## Exponentials

Functions are introduced and eliminated by lambda-abstraction and application.

        Δ; Γ.A ⊢ B
    λ   -------------
        Δ; Γ ⊢ A ⇒ B

        Δ; Γ ⊢ A ⇒ B   Δ; Γ ⊢ A
    app ------------------------
        Δ; Γ ⊢ B

Seems like we have to interpret _⇒_ as the usual exponential on presheaves.

Otherwise, for pointwise function space with A⁻, λ is not definable,
since Γ.A⁻ is not the right, thing, we need Γ.A.  (Cf. Two-dimensional
directed type theory by Licata and Harper (ENTCS 2011), where a
lambda/Π-introduced variable is negative, but only positive variables
can be used in a term, thus, λx.x is not even well-typed.)


## Sizes

Judgements

    Δ ⊢ s
    Δ ⊢ s ≤ s'

Rules

          Δ ⊢ s
    suc   ---------
          Δ ⊢ suc s

          Δ ⊢ s ≤ s'
    suc-l --------------
          Δ ⊢ s < suc s'

          Δ ⊢ s < s'
    suc-r ------------------
          Δ ⊢ suc s ≤ s'

Given a twin ordinal (α,β) ∈ O₂, what should be the successor?

          α ≤ α'  β' ≤ β
    suc-l ----------------------
          α < suc α'  β' < suc β

Thus, the usual successor should only apply to the covariant part.

    suc(α,β) = (α+1,β)

We could also have a "negative successor" applying to the contravariant part.

    suc⁻(α,β) = (α,β+1)

It acts like a predecessor, only that it does not cancel with the successor,
rather, it commutes with the successor.


But actually, rule suc-l does not hold on O₂ with _<_ defined as
leaving the second component fixed.  We would need β' = β there.




## Size quantification

         Δ,i; Wk₁ Γ ⊢ A
    λˢ   ---------------
         Δ ; Γ ⊢ ∀i.A

         Δ ; Γ ⊢ ∀i.A   Δ ⊢ s : Size
    appˢ ----------------------------
         Δ ; Γ ⊢ A[s/i]

Since we are interpreting variables in size contexts by pairs of ordinals,
the interpretation sσ : O₂ is also a pair of ordinals.

The quantifier ∀ can thus be defined pointwise (a simple limit)

    ∀ : PSh⟦Δ+1⟧ → PSh⟦Δ⟧
    ∀ A σ = ∀(α,β)∈O₂. A(σ,(α,β))

    ∀A(σ ≤ σ') : ∀Aσ → ∀Aσ'
    ∀A(σ ≤ σ') (a : ∀Aσ) (α,β) = A(σ',(α,β)) (a(α,β))

We may not need ends, which would be necessary if s was interpreted as
a single ordinal α, and we had to substitute it as (α,α).


## Subtyping

    Δ; Γ ⊢ A    Δ ⊢ A ≤ A'
    ----------------------
    Δ; Γ ⊢ A'

The subtyping derivation is interpreted as morphism

    (A≤A') : PSh⟦Δ⟧(A,A')

which can be composed with the morphism from the term

    t : PSh⟦Δ⟧(Γ,A)

to

    (A≤A') ∘ t : PSh⟦Δ](Γ,A')

### Contravariant function space

    Δ ⊢ A' ≤ A    Δ ⊢ B ≤ B'
    ------------------------
    Δ ⊢ (A → B) ≤ (A' → B')

    ((A → B) ≤ (A' → B')) σ (f : (A → B)σ) (σ' ≥ σ) (a : A'σ')
      = (B ≤ B')σ' (f σ' (A' ≤ A)σ' a)

    ((A → B) ≤ (A' → B')) σ (f : (A → B)σ) (σ' ≥ σ)
      = (B ≤ B')σ' ∘ f σ' ∘ (A' ≤ A)σ'

### Structural subtyping

If we only have structural subtyping, Aσ ≤ Aσ' for σ ≤ σ', then the
morphism we get from the subtyping derivation should be the
functoriality of A.

    (Aσ ≤ Aσ') = A(σ ≤ σ')

Structural subtyping is introduced by a single rule

    Δ' ⊢ A   Δ ⊢ σ ≤ σ' : Δ'
    ------------------------
    Δ ⊢ Aσ ≤ Aσ'

provided we have comparison of size substitutions  Δ ⊢ σ ≤ σ' : Δ'.


2019-02-26, Andreas
