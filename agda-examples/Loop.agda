{-# OPTIONS --experimental-irrelevance #-}

open import Base

--; --- Leibniz-equality

Eq : forall (A : Set) (a b : A) -> Set1 --;
Eq = \ A a b -> (P : A -> Set) -> P a -> P b

--; --- Reflexivity

refl : forall (A : Set) (a : A) -> Eq A a a --;
refl = \ A a P pa -> pa

--; --- Bottom type for Nat

Error : Set --;
Error = forall .i -> Nat i

--; --- Predecessor with default

pred : forall (error : Error) .i (x : Nat (i + 1)) -> Nat i --;
pred = \ error i -> \
       { (zero _) -> error i
       ; (suc _ x) -> x
       }

--;

shift : forall (error : Error) .i (g : Nat oo -> Nat (i + 1)) (n : Nat oo) -> Nat i --;
shift = \ error i g n -> pred error i (g (suc oo n))

--;

loop : forall (error : Error) .i (x : Nat i) (g : Nat oo -> Nat i) -> Nat oo --;
loop = \ error _ x ->
  fix (\ i _ -> (Nat oo -> Nat i) -> Nat oo)
      (\ i f -> \
        { (zero _ ) -> \ g -> f (shift error i g (zero oo))  (shift error i g)
        ; (suc _ y) -> \ g -> f (shift error i g (suc oo y)) (shift error i g)
        })
      x

--; --- Agda loops

diverge : forall (error : Error) -> Eq (Nat oo) (loop error oo (zero oo) (\ x -> x)) (zero oo) --;
diverge = \ error -> refl (Nat oo) (zero oo)
