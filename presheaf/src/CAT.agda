{-# OPTIONS --postfix-projections #-}

open import Library
open import Category

module CAT where

-- When are two functors equal?

module _ {o e h} (C D : Category o e h) where

  record FunEq (F G : Functor C D) : Set (o ⊔ h ⊔ e) where
    field
      eqApp : ∀{c} → F .App c ≡ G .App c  -- Strict, or maybe just isomorphism!?
      eqMap : ∀{c d} (f g : C .Hom c d) (eq : C .Eq f g) → let
          f' : D .Hom (G .App c) (G .App d)
          f' = subst₂ (D .Hom) eqApp eqApp (F .map f)
        in D .Eq f' (G .map g)
  open FunEq public

  funEqRefl : ∀ F → FunEq F F
  funEqRefl F .eqApp         = refl
  funEqRefl F .eqMap f g f=g = F .map-cong f=g

  funEqSym : ∀ F G → FunEq F G → FunEq G F
  funEqSym F G F=G .eqApp         = sym (F=G .eqApp)
  funEqSym F G F=G .eqMap f g f=g = {!f=g!}

  funEqTrans : ∀ F G H → FunEq F G → FunEq G H → FunEq F H
  funEqTrans F G H F=G G=H .eqApp = trans (F=G .eqApp) (G=H .eqApp)
  funEqTrans F G H F=G G=H .eqMap = {!!}

  funEquiv : IsEquivalence FunEq
  funEquiv .IsEquivalence.refl  = funEqRefl _
  funEquiv .IsEquivalence.sym   = funEqSym _ _
  funEquiv .IsEquivalence.trans = funEqTrans _ _ _

  funSetoid : Setoid (o ⊔ e ⊔ h) (o ⊔ e ⊔ h)
  funSetoid .Setoid.Carrier       = Functor C D
  funSetoid .Setoid._≈_           = FunEq
  funSetoid .Setoid.isEquivalence = funEquiv

  fun-comp-id-l : (F : Functor C D) → FunEq (compFun (idFun D) F) F
  fun-comp-id-l F .eqApp         = refl
  fun-comp-id-l F .eqMap f g f=g = F .map-cong f=g

  fun-comp-id-r : (F : Functor C D) → FunEq (compFun F (idFun C)) F
  fun-comp-id-r F .eqApp         = refl
  fun-comp-id-r F .eqMap f g f=g = F .map-cong f=g

  fun-comp-assoc : ∀ {A B : Category o e h}
                   (F : Functor B D) (G : Functor A B) (H : Functor C A) →
                 FunEq (compFun (compFun F G) H) (compFun F (compFun G H))
  fun-comp-assoc F G H .eqApp = refl
  fun-comp-assoc F G H .eqMap f g f=g = {!D !}

-- The category of categories

CAT : ∀ o e h → let l = o ⊔ e ⊔ h in Category (lsuc l) l l
CAT o e h .Obj        = Category o e h
CAT o e h .HomS C D   = funSetoid C D
CAT o e h .id         = idFun
CAT o e h .comp       = compFun
CAT o e h .comp-id-l  = fun-comp-id-l _ _ _
CAT o e h .comp-id-r  = fun-comp-id-r _ _ _
CAT o e h .comp-assoc = {!!}
CAT o e h .comp-cong  = {!!}

ΣCat : ∀{o e h} (C : Category o h e) (F : Functor C (CAT o e h)) → Category o (e ⊔ h) (e ⊔ h)
ΣCat C F .Obj  = Σ (C .Obj) λ c → F .App c .Obj
ΣCat C F .HomS (c , a) (d , b) .Setoid.Carrier = Σ (C .Hom c d) λ h → F .App d .Hom (F .map h .App a) b
ΣCat C F .HomS (c , a) (d , b) .Setoid._≈_ (h , f) (h' , f')    =
  Σ (C .Eq h' h) λ eq → F .App d .Eq f (subst (λ z → F .App d .Hom z b) (F .map-cong eq .eqApp {a}) f')
ΣCat C F .HomS (c , a) (d , b) .Setoid.isEquivalence = {!!}
ΣCat C F .id (c , a) =
  C .id c , subst (λ z → F .App c .Hom z a) (sym (F .map-id {c} .eqApp)) (F .App c .id a)
ΣCat C F .comp = {!!}
ΣCat C F .comp-id-l = {!!}
ΣCat C F .comp-id-r = {!!}
ΣCat C F .comp-assoc = {!!}
ΣCat C F .comp-cong = {!!}
