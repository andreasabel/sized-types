-- Andreas, 2017-02-18  Example from LMCS 2008 paper.
-- Freshly typed in for email exchange with Christophe Raffalli.

sized data Nat : +Size -> Set
{ zero : [i : Size] -> Nat (i + 1)
; suc  : [i : Size] -> Nat i -> Nat (i + 1)
}

sized data Hungry (A : Set) : +Size -> Set
{ inn : [i : Size] -> (A -> Hungry A i) -> Hungry A (i + 1)
}

fun out : [i : Size] [A : Set] -> Hungry A (i + 1) -> A -> Hungry A i
{ out .i A (inn i f) = f
}

fun  pred : [i : Size] -> Nat (i + 1) -> Nat i
{}

--  Hungry (Nat j) i  is lower semi continuous in  i
--  Proof:
--  Nat j -> X        antitone in i (even constant)
--  Nat j -> X        lsc in i by CONT-CONTRA
--  Hungry (Nat j) i  lsc in i by CONT-MU

fun s : [i, j : Size] -> Hungry (Nat j) i -> Hungry (Nat (j + 1)) i
{ s .$i j (inn i f) = inn i (\ n -> s i j (f (pred j n)))
}

fun p : [i, j : Size] -> Hungry (Nat (j + 1)) i -> Hungry (Nat j) i
{ p .$i j (inn i f) = inn i (\ n -> p i j (f (suc j n)))
}

fun tr : [i : Size] -> Hungry (Nat #) i -> [A : Set] -> A
{ tr .$i (inn i f) = tr i (p i # (f (suc # (zero #))))
}

fun h : [i : Size] -> Nat i -> Hungry (Nat i) i
{ h .$i (zero i)  = inn i (\ n -> s i i (h i (pred i n)))
; h .$i (suc i x) = inn i (\ n -> s i i (h i (pred i n)))
}

fun loop : [A : Set] -> A
{ loop = tr # (h # (zero #))
}
