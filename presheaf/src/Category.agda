{-# OPTIONS --postfix-projections #-}

open import Library

module Category where

-- Notation for Setoid fields

-- module HomSet {o h e} {Obj : Set o} (HomS : Obj → Obj → Setoid h e) where

--   module HomSetoid (A B : Obj) = Setoid (HomS A B)

--   open HomSetoid public using ()
--       renaming ( Carrier       to Hom )

--   module _ {A B : Obj} where
--     open HomSetoid A B public using ()
--       renaming ( _≈_           to EqH
--                ; isEquivalence to equivH
--                ; refl          to reflH
--                ; sym           to symH
--                ; trans         to transH
--                )

-- Category

record Category o h e : Set (lsuc (o ⊔ h ⊔ e)) where
  field
    Obj  : Set o
    HomS : (A B : Obj) → Setoid h e

  module EqReasoning {A B : Obj} = SetoidReasoning (HomS A B)

  open module HomSetoid  (A B : Obj) = Setoid (HomS A B)
    public using ()
    renaming ( Carrier       to Hom )

  open module HomSetoidH {A B : Obj} = HomSetoid A B
    public using ()
    renaming ( _≈_           to Eq
             ; isEquivalence to equiv
             ; refl          to reflEq
             ; sym           to symEq
             ; trans         to transEq
             )
  field
    id    : (A : Obj) → Hom A A
    comp  : ∀{A B C} (f : Hom B C) (g : Hom A B) → Hom A C

  field
    comp-id-l  : ∀{A B} {f : Hom A B} → Eq (comp (id B) f) f
    comp-id-r  : ∀{A B} {f : Hom A B} → Eq (comp f (id A)) f

    comp-assoc : ∀{A B C D} {f : Hom C D} {g : Hom B C} {h : Hom A B}
               → Eq (comp (comp f g) h) (comp f (comp g h))

    comp-cong  : ∀{A B C} {f f' : Hom B C} {g g' : Hom A B}
                 → Eq f f'
                 → Eq g g'
                 → Eq (comp f g) (comp f' g')


  comp-congˡ  : ∀{A B C} {f f' : Hom B C} {g : Hom A B}
               → Eq f f'
               → Eq (comp f g) (comp f' g)
  comp-congˡ eq = comp-cong eq reflEq

  comp-congʳ  : ∀{A B C} {f : Hom B C} {g g' : Hom A B}
               → Eq g g'
               → Eq (comp f g) (comp f g')
  comp-congʳ = comp-cong reflEq


open Category

-- Opposite category

op : ∀{o h e} (C : Category o h e) → Category o h e
op C .Obj            = C .Obj
op C .HomS A B       = C .HomS B A
op C .id A           = C .id A
op C .comp f g       = C .comp g f
op C .comp-id-l      = C .comp-id-r
op C .comp-id-r      = C .comp-id-l
op C .comp-assoc     = C .symEq (C .comp-assoc)
op C .comp-cong e e' = C .comp-cong e' e

-- Empty category

⊥-cat : ∀ o h e → Category o h e
⊥-cat o h e .Obj = Lift _ ⊥
⊥-cat o h e .HomS _ _ = ⊥-setoid _ _
⊥-cat o h e .id ()
⊥-cat o h e .comp ()
⊥-cat o h e .comp-id-l  {f = ()}
⊥-cat o h e .comp-id-r  {f = ()}
⊥-cat o h e .comp-assoc {f = ()}
⊥-cat o h e .comp-cong ()

-- Unit category

⊤-cat : ∀ o h e → Category o h e
⊤-cat o h e .Obj        = Lift _ ⊤
⊤-cat o h e .HomS _ _   = ⊤-setoid _ _
⊤-cat o h e .id         = _
⊤-cat o h e .comp       = _
⊤-cat o h e .comp-id-l  = _
⊤-cat o h e .comp-id-r  = _
⊤-cat o h e .comp-assoc = _
⊤-cat o h e .comp-cong  = _

-- Binary product category

_×-cat_ : ∀ {o1 h1 e1} (C1 : Category o1 h1 e1)
            {o2 h2 e2} (C2 : Category o2 h2 e2) → Category (o1 ⊔ o2) (h1 ⊔ h2) (e1 ⊔ e2)
(C1 ×-cat C2) .Obj                           = C1 .Obj × C2 .Obj
(C1 ×-cat C2) .HomS (A1 , A2) (B1 , B2)      = ×-setoid (C1 .HomS A1 B1) (C2 .HomS A2 B2)
(C1 ×-cat C2) .id (A1 , A2)                  = C1 .id A1 , C2 .id A2
(C1 ×-cat C2) .comp (f1 , f2) (g1 , g2)      = C1 .comp f1 g1 , C2 .comp f2 g2
(C1 ×-cat C2) .comp-id-l                     = C1 .comp-id-l , C2 .comp-id-l
(C1 ×-cat C2) .comp-id-r                     = C1 .comp-id-r , C2 .comp-id-r
(C1 ×-cat C2) .comp-assoc                    = C1 .comp-assoc , C2 .comp-assoc
(C1 ×-cat C2) .comp-cong (e1 , e2) (q1 , q2) = C1 .comp-cong e1 q1 , C2 .comp-cong e2 q2

-- I-ary product category

Π-cat : ∀{i o h e} {I : Set i} (C : I → Category o h e) → Category (i ⊔ o) (i ⊔ h) (i ⊔ e)
Π-cat C .Obj               = ∀ i → C i .Obj
Π-cat C .HomS A B = Π-setoid λ i → C i .HomS (A i) (B i)
Π-cat C .id A                  i = C i .id (A i)
Π-cat C .comp f g              i = C i .comp (f i) (g i)
Π-cat C .comp-id-l             i = C i .comp-id-l
Π-cat C .comp-id-r             i = C i .comp-id-r
Π-cat C .comp-assoc            i = C i .comp-assoc
Π-cat C .comp-cong f=f' g=g'   i = C i .comp-cong (f=f' i) (g=g' i)

-- Sets and functions

SET : ∀ o e → Category (lsuc (o ⊔ e)) (o ⊔ e) (o ⊔ e)
SET o e .Obj                                    = Setoid o e
SET o e .HomS S T                               = S ⇨ T
SET o e .id S                                   = FEq.id
SET o e .comp                                   = FEq._∘_
SET o e .comp-id-l  {f = f}                 x=y = FEq.cong f x=y
SET o e .comp-id-r  {f = f}                 x=y = FEq.cong f x=y
SET o e .comp-assoc {f = f} {g = g} {h = h} x=y = FEq.cong (f FEq.∘ (g FEq.∘ h)) x=y
SET o e .comp-cong  f=f' g=g'               x=y = f=f' (g=g' x=y)


-- Functor

record Functor {o1 h1 e1} (C1 : Category o1 h1 e1)
               {o2 h2 e2} (C2 : Category o2 h2 e2)
       : Set (o1 ⊔ h1 ⊔ e1 ⊔ o2 ⊔ h2 ⊔ e2) where
  field
    App : C1 .Obj → C2 .Obj

  private F = App
  field
    map : ∀{A B : C1 .Obj}
        → C1 .Hom A B
        → C2 .Hom (F A) (F B)

  field
    map-id   : ∀{A}
             → C2 .Eq (map (C1 .id A)) (C2 .id (F A))

    map-comp : ∀{A B C} {f : C1 .Hom B C} {g : C1 .Hom A B}
             → C2 .Eq (map (C1 .comp f g)) (C2 .comp (map f) (map g))

    map-cong : ∀{A B} {f f' : C1 .Hom A B}
             → C1 .Eq f f'
             → C2 .Eq (map f) (map f')

open Functor

-- Endofunctor

EndoFunctor : ∀{o h e} (C : Category o h e) → Set (o ⊔ h ⊔ e)
EndoFunctor C = Functor C C

-- Given a Functor F : C → D, the opposite functor op F : op C → op D
-- is the same functor with arrows in both categories considered reversed.

module _ {o1 h1 e1} (C1 : Category o1 h1 e1)
         {o2 h2 e2} (C2 : Category o2 h2 e2) where

  opFun : Functor C1 C2 → Functor (op C1) (op C2)
  opFun F .App      = F .App
  opFun F .map      = F .map
  opFun F .map-id   = F .map-id
  opFun F .map-comp = F .map-comp
  opFun F .map-cong = F .map-cong

-- Identity functor

idFun : ∀{o e h} (C : Category o e h) → Functor C C
idFun C .App      = Function.id
idFun C .map      = Function.id
idFun C .map-id   = C .reflEq
idFun C .map-comp = C .reflEq
idFun C .map-cong = Function.id

-- Functor composition

compFun : ∀ {o1 o2 o3 e1 e2 e3 h1 h2 h3}
            {C1 : Category o1 e1 h1}
            {C2 : Category o2 e2 h2}
            {C3 : Category o3 e3 h3}
        → (F : Functor C2 C3) (G : Functor C1 C2) → Functor C1 C3
compFun F G .App A                  = F .App (G .App A)
compFun F G .map f                  = F .map (G .map f)
compFun {C3 = C} F G .map-id        = C .transEq (F .map-cong (G .map-id)) (F .map-id)
compFun {C3 = C} F G .map-comp      = C .transEq (F .map-cong (G .map-comp)) (F .map-comp)
compFun {C3 = C} F G .map-cong f=f' = F .map-cong (G .map-cong f=f')

-- Projection from the product category is a functor

projFun : ∀ {i o e h} {I : Set i} (C : I → Category o e h)
        → (i : I)
        → Functor (Π-cat C) (C i)
projFun C i .App A         = A i
projFun C i .map f         = f i
projFun C i .map-id        = C i .reflEq
projFun C i .map-comp      = C i .reflEq
projFun C i .map-cong f=f' = f=f' i

-- Natural transformations

module _ {o1 h1 e1} {C : Category o1 h1 e1}
         {o2 h2 e2} {D : Category o2 h2 e2} where

  module _ (F G : Functor C D) where

    record NaturalTransformation : Set (o1 ⊔ h1 ⊔ e1 ⊔ o2 ⊔ h2 ⊔ e2) where
      field
        transformation : ∀{A} → D .Hom (F .App A) (G .App A)

      field
        naturality : ∀{A B} (f : C .Hom A B)
                   → D .Eq (D .comp transformation (F .map f))
                           (D .comp (G .map f) transformation)

      -- Naturality in the other direction
      naturality⁻¹ :  ∀{A B} (f : C .Hom A B)
                     → D .Eq (D .comp (G .map f) transformation)
                             (D .comp transformation (F .map f))
      naturality⁻¹ = λ f → D .symEq (naturality f)

    open NaturalTransformation

    -- The equality on natural transformations
    -- is pointwise and ignores the proof of naturality.

    nat-setoid : Setoid (o1 ⊔ h1 ⊔ e1 ⊔ o2 ⊔ h2 ⊔ e2) (o1 ⊔ e2)
    nat-setoid .Setoid.Carrier = NaturalTransformation
    nat-setoid .Setoid._≈_ ϕ ψ = ∀{A} → D .Eq (ϕ .transformation {A}) (ψ .transformation {A})
    nat-setoid .Setoid.isEquivalence .IsEquivalence.refl         = D .reflEq
    nat-setoid .Setoid.isEquivalence .IsEquivalence.sym   eq     = D .symEq   eq
    nat-setoid .Setoid.isEquivalence .IsEquivalence.trans eq eq' = D .transEq eq eq'

  open NaturalTransformation

  -- Identity natural transformation.

  idNat : ∀ (F : Functor C D) → NaturalTransformation F F
  idNat F .transformation {A} = D .id (F .App A)
  idNat F .naturality     f   = D .transEq (D .comp-id-l) (D .symEq (D .comp-id-r))

  -- Natural transformation composition.

  compNat : ∀ {F G H : Functor C D}
            (ϕ : NaturalTransformation G H) (ψ : NaturalTransformation F G) → NaturalTransformation F H
  compNat {F} {G} {H} ϕ ψ .transformation {A} = D .comp (ϕ .transformation {A}) (ψ .transformation {A})
  compNat {F} {G} {H} ϕ ψ .naturality {A = A} {B = B} f = begin
      (ϕB ∘ ψB) ∘ F .map f   ≈⟨ D .comp-assoc ⟩
      ϕB ∘ (ψB ∘ F .map f)   ≈⟨ D .comp-cong (D .reflEq) (ψ .naturality f) ⟩
      ϕB ∘ (G .map f ∘ ψA)   ≈⟨ D .symEq (D .comp-assoc) ⟩
      (ϕB ∘ G .map f) ∘ ψA   ≈⟨ D .comp-cong (ϕ .naturality f) (D .reflEq) ⟩
      (H .map f ∘ ϕA) ∘ ψA   ≈⟨ D .comp-assoc ⟩
      H .map f ∘ (ϕA ∘ ψA)   ∎
    where
    open SetoidReasoning (D .HomS (F .App A) (H .App B))
    _∘_ = D .comp
    ϕA = ϕ .transformation {A}
    ϕB = ϕ .transformation {B}
    ψA = ψ .transformation {A}
    ψB = ψ .transformation {B}

-- Functor categories

module _ {o1 h1 e1} (C : Category o1 h1 e1)
         {o2 h2 e2} (D : Category o2 h2 e2) where

  functor-cat : Category _ _ _ -- Category (o1 ⊔ h1 ⊔ e1 ⊔ o2 ⊔ h2 ⊔ e2) (o1 ⊔ h1 ⊔ e1 ⊔ o2 ⊔ h2 ⊔ e2) (o1 ⊔ e2)
  functor-cat .Obj                  = Functor C D
  functor-cat .HomS F G             = nat-setoid F G
  functor-cat .id F                 = idNat F
  functor-cat .comp ϕ ψ             = compNat ϕ ψ
  functor-cat .comp-id-l            = D .comp-id-l
  functor-cat .comp-id-r            = D .comp-id-r
  functor-cat .comp-assoc           = D .comp-assoc
  functor-cat .comp-cong  f=f' g=g' = D .comp-cong f=f' g=g'


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
