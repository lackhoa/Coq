Require Import List.

Definition Decidable (T: Type):= forall (n m: T),
  n = m \/ n <> m.

Theorem In_Decidable: forall (T: Type) (l: list T) (n: T),
   Decidable T ->
  In n l \/ ~ In n l.
Proof. induction l; intros.
- right. auto.
- assert (In n l \/ ~ In n l).
{ apply (IHl n). auto. }
destruct H0.
  + left. simpl. right. assumption.
  + simpl. assert (a = n \/ a <> n).
  { apply (H a n). }
  destruct H1.
    * left. left; assumption.
    * right. intro. destruct H2. apply H1 in H2; auto.
    apply H0 in H2; auto. Qed.

(*Now we can prove the Dirichlet principle with this result*)