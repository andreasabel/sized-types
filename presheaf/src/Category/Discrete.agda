{-# OPTIONS --postfix-projections #-}

open import Library
open import Category

module Category.Discrete where

open Category.Category
open Functor

-- The only arrows in a discrete category are the identity arrows.
-- Hom A B = A ≡ B

module _ {i} (I : Set i) where

  discrete : Category i i i
  discrete .Obj                   = I
  discrete .HomS A B              = setoid (A ≡ B)
  discrete .id A                  = refl
  discrete .comp f g              = trans g f
  discrete .comp-id-l {f = refl}  = refl
  discrete .comp-id-r             = refl
  discrete .comp-assoc {h = refl} = refl
  discrete .comp-cong refl refl   = refl

  module _ {o h e} (C : Category o h e) where

    DiscreteFunctor = Functor discrete C

    -- A functor from a discrete category is given by the object part,
    -- since the morphism part is trivial.

    module _ (f : I → C .Obj) where

      discreteFunctor : DiscreteFunctor
      discreteFunctor .App                 = f
      discreteFunctor .map refl            = C .id _
      discreteFunctor .map-id              = C .reflEq
      discreteFunctor .map-comp {g = refl} = C .symEq (C .comp-id-r)
      discreteFunctor .map-cong refl       = C .reflEq
