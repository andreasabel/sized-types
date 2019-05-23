{-# OPTIONS --postfix-projections #-}

open import Library
open import Category
open import Presheaf

module Presheaf.Properties where

module _ {o h e} {C : Category o h e} where

  ⊤-presheaf-terminal : ∀{s} → Terminal (presheaf-cat s C) (⊤-presheaf _ _ C)
  ⊤-presheaf-terminal = _

  ⊥-presheaf-initial : ∀{s} → Initial (presheaf-cat s C) (⊥-presheaf _ _ C)
  ⊥-presheaf-initial .! A .transformation B ._⟨$⟩_ ()
  ⊥-presheaf-initial .! A .transformation B .FEq.cong ()
  ⊥-presheaf-initial .! A .naturality f ()
  ⊥-presheaf-initial .!-unique f A ()
