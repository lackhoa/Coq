Require Import Arith.
Require Import Nat.
Require Import List.

Inductive reflect (P: Prop) (b: bool) :  Prop :=
  | ReflectT: (P /\ (b = true))-> reflect P b
  | ReflectF: (~P /\ (b = false)) -> reflect P b.

Theorem reflect_iff: forall P b,
  reflect P b <-> (P <-> b = true).
Proof. split.
- intros. inversion H; destruct H0.
  + split; auto.
  + split; auto. intro. rewrite H1 in H2. inversion H2.
- intros. inversion H. destruct b.
  + apply ReflectT. split; auto.
  + apply ReflectF. split; auto. intro. apply H0 in H2.
  inversion H2.
Qed.

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

Definition simple_reflect (P: Prop) (b: bool) : Prop :=
  (P /\ b = true) \/ (~P /\ b = false).

Theorem simple_reflect_iff: forall P b,
  simple_reflect P b <-> (P <-> b = true).
Proof. intros. split; intros.
- inversion H; destruct H0; auto.
  + split; auto. + split; auto. intro. rewrite H1 in H2; inversion H2.
- destruct H. unfold simple_reflect. destruct b.
  + left; auto. + right; auto. split; auto.
  intro. apply H in H1; inversion H1. Qed.

Theorem simple_beq_natP : forall n m,
  simple_reflect (n = m) (n =? m).
Proof. intros. apply simple_reflect_iff.
symmetry. apply Nat.eqb_eq. Qed.

Theorem simple_beq_natP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof. induction l; intros.
- intro. inversion H0.
- intro. inversion H. destruct (simple_beq_natP n a); destruct H1.
  + rewrite H3 in H2. inversion H2.
  + rewrite H3 in H2. inversion H2. 
  apply IHl in H5. apply H5. inversion H0.
    * subst. exfalso; apply H1. auto.
    * auto. Qed.











