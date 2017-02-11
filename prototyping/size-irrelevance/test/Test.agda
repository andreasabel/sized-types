--- Sample Sit file

{-# OPTIONS --experimental-irrelevance #-}

open import Base

--; --- Leibniz-equality

Eq : forall (A : Set) (a b : A) -> Set1 --;
Eq = \ A a b -> (P : A -> Set) -> P a -> P b

--; --- Reflexivity

refl : forall (A : Set) (a : A) -> Eq A a a --;
refl = \ A a P pa -> pa

--; --- Symmetry

sym : forall (A : Set) (a b : A) -> Eq A a b -> Eq A b a --;
sym = \ A a b eq P pb ->  eq (\ x -> P x -> P a) (\ pa -> pa) pb
--- sym = \ A a b eq -> eq (\ x -> Eq A x a) (refl A a)

--; --- Transitivity

trans : forall (A : Set) (a b c : A) -> Eq A a b -> Eq A b c -> Eq A a c --;
trans = \ A a b c p q P pa -> q P (p P pa)

--; --- Congruence

cong : forall (A B : Set) (f : A -> B) (a a' : A) -> Eq A a a' -> Eq B (f a) (f a') --;
cong = \ A B f a a' eq P pfa -> eq (\ x -> P (f x)) pfa

--; --- Addition

plus : forall .i -> Nat i -> Nat oo -> Nat oo --;
plus = \ i x y ->
  fix (\ i x -> Nat oo)
      (\ f -> \
---      (\ f x -> case x return (\ _ -> Nat oo) of \
              { zero    -> y
              ; (suc x) -> suc (f x)
              })
      x
  --;

plus' : forall .i -> Nat i -> Nat oo -> Nat oo  --;
plus' = \ i x ->
  fix (\ i x -> Nat oo -> Nat oo)
---           (\ f x -> case x return (\ _ -> Nat oo -> Nat oo) of \
      (\ f -> \
         { zero    -> \ y -> y
         ; (suc x) -> \ y -> suc (f x y)
         })
      x

--; --- Predecessor

pred  : forall .i -> Nat i -> Nat i  --;
pred = \ _ -> \{ zero -> zero; (suc y) -> y }

--; --- Subtraction

{- {- Agda does not like the following -}
minus : forall .i -> Nat i -> forall .j -> Nat j -> Nat i --;
minus = \ i x j y ->
  fix (\ _ _ -> Nat i -> Nat i)  --- Variable i is declared irrelevant, so it cannot be used here
      (\ f -> \{ zero -> \ x -> x; (suc y) -> \ x -> f y (pred i x) })
      y
      x
  --;
--- -}

sub : forall .j -> Nat j -> forall .i -> Nat i -> Nat i  --;
sub = \ j y ->
  fix (\ _ _ -> forall .i -> Nat i -> Nat i)
      (\ f -> \ { zero -> \ i x -> x; (suc y) -> \ i x -> f y i (pred i x) }) --- pred i (f y i x) })
      y

--; --- Lemma: x - x == 0

sub_diag : forall .i (x : Nat i) -> Eq (Nat oo) (sub i x i x) zero  --;
sub_diag = \ i x ->
  fix (\ i x -> Eq (Nat oo) (sub i x i x) zero)
      (\ f -> \{ zero -> refl (Nat oo) zero ; (suc y) -> f y })
      x

--; ---
