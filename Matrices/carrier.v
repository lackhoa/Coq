Require Export ZArithRing.
Require Export ZArith.

Module Type Carrier.
Parameter A : Set.
Parameter Aopp : A -> A.
Parameters (Aplus Aminus Amult: A -> A -> A).
Parameters (A0 : A) (A1 : A).

Axiom A_ring : ring_theory A0 A1 Aplus Amult Aminus Aopp (eq(A:=A)).

End Carrier.

Module Zc : Carrier.

Definition A := Z.
Definition Aopp := Zopp.
Definition Aplus := Zplus.
Definition Aminus := Zminus.
Definition Amult := Zmult.
Definition A0 := 0%Z.
Definition A1 := 1%Z.

Definition A_ring := InitialRing.Zth.

End Zc.
