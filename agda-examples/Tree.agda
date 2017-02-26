module Tree where

  open import Size
  open import Function

  data Tree (A B : Set) : Size → Set where
    leaf : ∀{i} (a : A) → Tree A B (↑ i)
    node : ∀{i} (b : B) (l r : Tree A B i) → Tree A B (↑ i)

  -- Generic tree modification traversal

  gmap : ∀{A B}
    (pre  : ∀{i} → Tree A B i → Tree A B i)
    (post :         Tree A B ∞ → Tree A B ∞)
    → ∀{i} (t : Tree A B i) → Tree A B ∞
  gmap pre post t = post $ case pre t of \
    { (leaf a)     → leaf a
    ; (node b l r) → node b (gmap pre post l) (gmap pre post r)
    }
