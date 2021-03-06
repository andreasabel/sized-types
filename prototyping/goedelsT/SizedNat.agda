-- Sized Gödel's T and its embedding into MLTT = Agda

module SizedNat where

open import Data.Maybe
open import Data.Sum renaming (inj₁ to left; inj₂ to right)

open import Data.Nat renaming (z≤n to z≤; decTotalOrder to decTotalOrderℕ)
open import Data.Nat.Properties using (_+-mono_; ≤-step; ≤⇒pred≤)

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Relation.Nullary
open import Relation.Binary using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

module ≤ℕ = DecTotalOrder decTotalOrderℕ

-- Some properties of ≤ℕ.

pred≤ : ∀{i j} → suc i ≤ suc j → i ≤ j
pred≤ (s≤s p) = p

case≤′ : (P : (i j : ℕ) → Set)
      → ∀ {i j} → .(suc i ≤ j)
      → (∀ {i j} → .(i ≤ j) → P i (suc j))
      → P i j
case≤′ P {j = zero}  ()
case≤′ P {j = suc j} si≤sj k = k (pred≤ si≤sj)

case≤ : ∀{i} → (P : (j : ℕ) → Set)
      → ∀ {j} → .(suc i ≤ j)
      → (∀ {j} → .(i ≤ j) → P (suc j))
      → P j
case≤ P {j = zero}  ()
case≤ P {j = suc j} si≤sj k = k (pred≤ si≤sj)

-- Sizes are natural numbers.

Size = ℕ

-- Sized natural numbers.

record SNat (size : Size) : Set where
  constructor snat
  field
    nat      : ℕ
    .bounded : nat ≤ size

-- Subtyping

embSNat : ∀ {i j} → .(i ≤ j) → SNat i → SNat j
embSNat i≤j (snat n n≤i) = snat n (≤ℕ.trans n≤i i≤j)

-- Retract

convSNat- : ∀ {i j} → SNat i → Maybe (SNat j)
convSNat- {i} {j} (snat n n≤i) with i ≤? j
convSNat- (snat n n≤i) | yes i≤j = just (snat n (≤ℕ.trans n≤i i≤j))
convSNat- (snat n n≤i) | no  i≰j = nothing

convSNat : ∀ {i j} → SNat i → (i ≰ j) ⊎ SNat j
convSNat {i} {j} (snat n n≤i) with i ≤? j
convSNat (snat n n≤i) | yes i≤j = right (snat n (≤ℕ.trans n≤i i≤j))
convSNat (snat n n≤i) | no  i≰j = left i≰j

-- Zero and successor

zeroSNat : ∀ {i} → SNat i
zeroSNat = snat zero z≤

sucSNat : ∀ {i} → SNat i → SNat (suc i)
sucSNat (snat n n≤i) = snat (suc n) (s≤s n≤i)

-- Predecessor

predSNat : ∀ {i} → SNat i → SNat i
predSNat (snat 0         0≤i) = snat 0 0≤i
predSNat (snat (suc n) 1+n≤i) = snat n (≤⇒pred≤ _ _ 1+n≤i)
-- predSNat (snat (suc n) 1+n≤i) = case≤′ (λ _ → SNat) 1+n≤i
--   λ {n} n≤i-1 → snat n (≤-step n≤i-1)

-- Simple iteration

iterSNat : ∀ {A : Set}{i} → SNat i → (A → A) → A → A
iterSNat (snat n _) f a = fold a f n

-- Subtraction

minusSNat : ∀{i} → SNat i → ∀{j} → SNat j → SNat i
minusSNat n m = iterSNat m predSNat n

-- Euclidian Division n / suc m
-- div 0 m = 0
-- div (suc n) m = suc (div (n - m) m)

module NonTerm where

  -- Not termination checking without case on size i.
  {-# NO_TERMINATION_CHECK #-}
  divSNat : ∀{i} → SNat i → ∀{j} → SNat j → SNat i
  divSNat (snat 0         0≤i) m = snat 0 0≤i
  divSNat (snat (suc n) 1+n≤i) m = case≤ SNat 1+n≤i
    λ n≤i-1 → sucSNat (divSNat (minusSNat (snat n n≤i-1) m) m)

-- We need to case on the size to demonstrate termination.

divSNat : ∀{i} → SNat i → ∀{j} → SNat j → SNat i
divSNat         (snat 0       0≤i)     m = snat 0 0≤i
divSNat {i = 0} (snat (suc n) ())
divSNat {suc i} (snat (suc n) 1+n≤1+i) m =
  sucSNat (divSNat (minusSNat (snat n (pred≤ 1+n≤1+i)) m) m)

-- Simple types (Gödel's T)

data Ty : Set where
  N̂   : Ty
  _→̂_ : (T U : Ty) → Ty

El : Ty → Set
El N̂       = ℕ
El (T →̂ U) = El T → El U

-- A grammar for sized types in Gödel's T

-- Size expressions in types

SCxt = ℕ
SVar = Fin

data SExpr (Δ : SCxt) : Set where
  zero :                 SExpr Δ
  suc  : (a : SExpr Δ) → SExpr Δ
  var  : (x : SVar  Δ) → SExpr Δ

-- Interpretation of size expressions

SEnv : SCxt → Set
SEnv = Vec Size

sval : ∀{Δ} → SEnv Δ → SExpr Δ → Size
sval ρ zero    = 0
sval ρ (suc a) = suc (sval ρ a)
sval ρ (var x) = lookup x ρ

-- Simple sized types

data STy : (Δ : SCxt) → Set where
  Nˢ   : ∀{Δ} (a   : SExpr Δ)     → STy Δ
  _→ˢ_ : ∀{Δ} (T U : STy Δ)       → STy Δ
  ∀ˢ   : ∀{Δ} (T   : STy (suc Δ)) → STy Δ
  Wkˢ  : ∀{Δ} (T   : STy Δ)       → STy (suc Δ)
  Clˢ  : ∀{Δ} (T   : STy 0)       → STy Δ  -- closed types

SEl : ∀{Δ} → SEnv Δ → STy Δ → Set
SEl ρ (Nˢ a)   = SNat (sval ρ a)
SEl ρ (T →ˢ U) = SEl ρ T → SEl ρ U
SEl ρ (∀ˢ T)   = ∀{i} → SEl (i ∷ ρ) T
SEl (_ ∷ ρ) (Wkˢ T)  = SEl ρ T
SEl ρ (Clˢ T)  = SEl [] T

-- wk : ∀{Δ} → STy Δ → STy (suc Δ)
-- wk (Nˢ a) = {!!}
-- wk (T →ˢ T₁) = {!!}
-- wk (∀ˢ T) = {!!}
-- wk (Clˢ T) = {!!}

-- Underlying type

uty : ∀{Δ} → STy Δ → Ty
uty (Nˢ a)    = N̂
uty (T →ˢ U)  = uty T →̂ uty U
uty (∀ˢ T)    = uty T
uty (Wkˢ T)   = uty T
uty (Clˢ T)   = uty T

-- Logical relation between sized things and unsized things
-- Ignores sizes

LRu : ∀{Δ} (T : STy Δ) (ρ : SEnv Δ) → SEl ρ T → El (uty T) → Set
LRu (Nˢ a)   ρ (snat n _) e = n ≡ e
LRu (U →ˢ T) ρ t e = ∀ u d → LRu U ρ u d → LRu T ρ (t u) (e d)
LRu (∀ˢ T)   ρ t e = ∀ i → LRu T (i ∷ ρ) (t {i}) e
LRu (Wkˢ T)  (_ ∷ ρ) t e = LRu T ρ t e
LRu (Clˢ T)  ρ t e = LRu T [] t e

module Trivial where

  -- Logical relation between sized things of same size
  -- Ignores sizes

  LR : ∀{Δ} (ρ : SEnv Δ) (T : STy Δ) → (t t' : SEl ρ T) → Set
  LR ρ (Nˢ a)   t t' = SNat.nat t ≡ SNat.nat t'
  LR ρ (U →ˢ T) t t' = ∀ u u' → LR ρ U u u' → LR ρ T (t u) (t' u')
  LR ρ (∀ˢ T)   t t' = ∀ i → LR (i ∷ ρ) T (t {i}) (t' {i})
  LR (_ ∷ ρ) (Wkˢ T) t t' = LR ρ T t t'
  LR ρ (Clˢ T)  t t' = LR [] T t t'

  -- Good programs are those which are in the LR

  Good : ∀{Δ} (ρ : SEnv Δ) (T : STy Δ) (t : SEl ρ T) → Set
  Good ρ T t = LR ρ T t t

  -- Zero is good

  styZero : ∀{Δ} → STy Δ
  styZero = ∀ˢ (Nˢ (var zero))

  goodZero : ∀{Δ}{ρ : SEnv Δ} → Good ρ styZero zeroSNat
  goodZero = λ i → ≡.refl

  -- Suc is good

  stySuc : ∀{Δ} → STy Δ
  stySuc = ∀ˢ (Nˢ (var zero) →ˢ Nˢ (suc (var zero)))

  goodSuc : ∀{Δ}{ρ : SEnv Δ} → Good ρ stySuc sucSNat
  goodSuc i n n' n≡n' = ≡.cong suc n≡n'

  -- Pred is good

  styPred : ∀{Δ} → STy Δ
  styPred = ∀ˢ (Nˢ (var zero) →ˢ Nˢ (var zero))

  goodPred : ∀{Δ}{ρ : SEnv Δ} → Good ρ styPred predSNat
  goodPred i (snat n _) (snat .n _) ≡.refl = ≡.refl

  -- Minus is good

  styMinus : ∀{Δ} → STy Δ
  styMinus = ∀ˢ (Nˢ (var zero) →ˢ ∀ˢ (Nˢ (var zero) →ˢ Nˢ (var (suc zero))))

  goodMinus : ∀{Δ}{ρ : SEnv Δ} → Good ρ styMinus minusSNat
  goodMinus i (snat n _) (snat .n _) ≡.refl j (snat m _) (snat .m _) ≡.refl = ≡.refl

  -- Div is good

  styDiv : ∀{Δ} → STy Δ
  styDiv = ∀ˢ (Nˢ (var zero) →ˢ ∀ˢ (Nˢ (var zero) →ˢ Nˢ (var (suc zero))))

  goodDiv : ∀{Δ}{ρ : SEnv Δ} → Good ρ styDiv divSNat
  goodDiv i (snat n _) (snat .n _) ≡.refl j (snat m _) (snat .m _) ≡.refl = ≡.refl


-- Heterogeneous logical relation between sized things
-- Ignores sizes

LR : ∀{Δ} (T : STy Δ) (ρ ρ' : SEnv Δ) → SEl ρ T → SEl ρ' T → Set
LR (Nˢ a)   ρ ρ' t t' = SNat.nat t ≡ SNat.nat t'
LR (U →ˢ T) ρ ρ' t t' = ∀ u u' → LR U ρ ρ' u u' → LR T ρ ρ' (t u) (t' u')
LR (∀ˢ T)   ρ ρ' t t' = ∀ i i' → LR T (i ∷ ρ) (i' ∷ ρ') (t {i}) (t' {i'})
LR (Wkˢ T)  (_ ∷ ρ) (_ ∷ ρ') t t' = LR T ρ ρ' t t'
LR (Clˢ T)  ρ ρ' t t' = LR T [] [] t t'

-- LR is a PER on Σ (SEnv Δ) (λ ρ → SEl ρ T)

-- For reflexivity, we probably need coerce/coherence

-- Good programs are closed ones which are in the LR

ClTy = STy 0

Good : (T : STy 0) (t : SEl [] T) → Set
Good T t = LR T [] [] t t

-- Zero is good

styZero : ClTy
styZero = ∀ˢ (Nˢ (var zero))

goodZero : Good styZero zeroSNat
goodZero = λ i i' → ≡.refl

-- Suc is good

stySuc : ClTy
stySuc = ∀ˢ (Nˢ (var zero) →ˢ Nˢ (suc (var zero)))

goodSuc : Good stySuc sucSNat
goodSuc i i' n n' n≡n' = ≡.cong suc n≡n'

-- Pred is good

styPred : ClTy
styPred = ∀ˢ (Nˢ (var zero) →ˢ Nˢ (var zero))

goodPred : Good styPred predSNat
goodPred i i' (snat zero    _) (snat zero     _) _ = ≡.refl
goodPred i i' (snat zero    _) (snat (suc _)  _) ()
goodPred i i' (snat (suc _) _) (snat zero     _) ()
goodPred i i' (snat (suc n) _) (snat (suc .n) _) ≡.refl = ≡.refl

-- Iter is good (needs parametricity)

postulate
  iterGood : ∀{Δ} (T : STy Δ) (ρ ρ' : SEnv Δ) →
    LR (∀ˢ (Nˢ (var zero) →ˢ let T' = Wkˢ T in ((T' →ˢ T') →ˢ (T' →ˢ T')))) ρ ρ'
       (iterSNat {SEl ρ T}) (iterSNat {SEl ρ' T})
  -- iterGood T i i' (snat n _) (snat .n _) ≡.refl = {!!}

-- Minus is good

styMinus : ClTy
styMinus = ∀ˢ (Nˢ (var zero) →ˢ ∀ˢ (Nˢ (var zero) →ˢ Nˢ (var (suc zero))))

goodMinus : Good styMinus minusSNat
goodMinus i i' n n' n≡n' j j' m m' m≡m' =
  iterGood (Nˢ (var zero)) (i ∷ []) (i' ∷ [])
    j j' m m' m≡m'
    predSNat predSNat (goodPred i i')
    n n' n≡n'

-- Div is good

styDiv : ClTy
styDiv = ∀ˢ (Nˢ (var zero) →ˢ ∀ˢ (Nˢ (var zero) →ˢ Nˢ (var (suc zero))))

goodDiv : Good styDiv divSNat
goodDiv i i'      (snat 0 _) (snat .0 _) ≡.refl _ _ _ _ _ = goodZero i i'
goodDiv 0 _       (snat (suc _) ())
goodDiv (suc _) 0 (snat (suc n)  _) (snat .(suc n) ()) ≡.refl
goodDiv (suc i) (suc i') (snat (suc n) _) (snat .(suc n) _) ≡.refl
  j j' m m' m≡m'
  = goodSuc i i'
      (divSNat (minusSNat (snat n _) m ) m )
      (divSNat (minusSNat (snat n _) m') m')
      (goodDiv i i'
         (minusSNat (snat n _) m )
         (minusSNat (snat n _) m')
         (goodMinus i i' (snat n _  ) (snat n _   ) ≡.refl
                    j j' m m' m≡m')
         j j' m m' m≡m')


