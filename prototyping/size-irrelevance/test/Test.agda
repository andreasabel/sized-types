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
      (\ _ f -> \
---      (\ _ f x -> case x return (\ _ -> Nat oo) of \
              { (zero _)   -> y
              ; (suc _ x) -> suc oo (f x)
              })
      x

--; --- Reduction rules for plus

plus_red_zero : forall .i (y : Nat oo) -> Eq (Nat oo) (plus (i + 1) (zero i) y) y  --;
plus_red_zero = \ i y -> refl (Nat oo) y  --;

plus_red_suc : forall .i (x : Nat i) (y : Nat oo) -> Eq (Nat oo) (plus (i + 1) (suc i x) y) (suc oo (plus i x y))  --;
plus_red_suc = \ i x y -> refl (Nat oo) (suc oo (plus i x y))  --;

--; --- Another definition of addition

plus' : forall .i -> Nat i -> Nat oo -> Nat oo  --;
plus' = \ i x ->
  fix (\ i x -> Nat oo -> Nat oo)
---           (\ f x -> case x return (\ _ -> Nat oo -> Nat oo) of \
      (\ _ f -> \
         { (zero _)  -> \ y -> y
         ; (suc _ x) -> \ y -> suc oo (f x y)
         })
      x

--; --- Predecessor

--- pred  : forall .i -> Nat i -> Nat i  --;
--- pred = \ _ -> \{ (zero _) -> zero _ ; (suc _ y) -> y }

pred  : forall .i -> Nat i -> Nat i  --;
pred = \ i n ->
  fix (\ i _ -> Nat i)
      (\ i _ -> \{ (zero _) -> zero i ; (suc _ y) -> y })
      n

--; --- Subtraction

--- {- {- Agda does not like the following -}
--- minus : forall .i -> Nat i -> forall .j -> Nat j -> Nat i --;
--- minus = \ i x j y ->
---   fix (\ _ _ -> Nat i -> Nat i)  --- Variable i is declared irrelevant, so it cannot be used here
---       (\ _ f -> \{ (zero _) -> \ x -> x; (suc _ y) -> \ x -> f y (pred i x) })
---       y
---       x
---   --;
--- --- -}

sub : forall .j -> Nat j -> forall .i -> Nat i -> Nat i  --;
sub = \ j y ->
  fix (\ _ _ -> forall .i -> Nat i -> Nat i)
      (\ _ f -> \ { (zero _) -> \ i x -> x; (suc _ y) -> \ i x -> f y i (pred i x) }) --- pred i (f y i x) })
      y

--; --- Lemma: x - x == 0

sub_diag : forall .i (x : Nat i) -> Eq (Nat oo) (sub i x i x) (zero oo)  --;
sub_diag = \ i x ->
  fix (\ i x -> Eq (Nat oo) (sub i x i x) (zero oo))
      (\ _ f -> \{ (zero _) -> refl (Nat oo) (zero oo) ; (suc _ y) -> f y })
      x

--; ---
