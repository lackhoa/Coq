Require Import Arith.
Require Import Nat.
Require Import List.

Inductive reflect (P: Prop) : bool -> Prop :=
  | ReflectT: P -> reflect P true
  | ReflectF: ~P -> reflect P false.

Theorem reflect_iff: forall P b,
  reflect P b <-> (P <-> b = true).
Proof. split.
- intros. inversion H.
  + split; auto.
  + split; auto. intros. inversion H2.
- intros. destruct b.
  + apply ReflectT. apply H. auto.
  + apply ReflectF. intro. apply H in H0. inversion H0.
Qed.

Theorem lebP : forall n m, reflect (le n m) (leb n m).
Proof. intros. apply reflect_iff.
Require Import Omega. split.
- apply leb_correct.
- apply leb_complete. Qed.

Fixpoint count n l :=
  match l with
  | nil => 0
  | cons m l' => (if (beq_nat n m) then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof. induction l; intros.
- intro. inversion H0.
- intro. inversion H. destruct (Nat.eqb_spec n a).
  + inversion H2.
  + inversion H2. apply IHl in H3. apply H3. inversion H0.
    * destruct n0. auto.
    * auto. Qed.












