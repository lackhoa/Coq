Add LoadPath "/home/khoa/Coq/sf".
Require Import Maps.
Require Import Types.
Require Import Smallstep.
Require Import Stlc.
Require Import StlcProp.

Module STLCHalt.
Import STLC.
Import STLCProp.
Require Import Omega.

Definition tm_context := partial_map tm.

Definition wtyped_empty (t: tm): Prop :=
  exists T, empty |- t \in T.

Definition normalizing (P: tm -> Prop) (t: tm): Prop :=
  exists t', t ==>* t' /\ P t'.

Fixpoint adapt (Sigma: tm_context) (t: tm): tm :=
  match t with
  | tvar x => match (Sigma x) with
    | Some s => s
    | None => t
    end
  (*Note: beq_id is done with map lookup*)

  | tapp t1 t2 =>
    tapp (adapt Sigma t1) (adapt Sigma t2)

  | tabs x T t1 =>
    tabs x T (adapt (t_update Sigma x None) t1)
  (*x is bound to the abstraction so exclude it from the map*)
  (*Again: beq_id is done with map lookup*)

  | ttrue => t
  | tfalse => t
  | tif t1 t2 t3 => tif (adapt Sigma t1) (adapt Sigma t2) (adapt Sigma t3)
  end.

(*Some more map trivials (why are we doing this again?)*)
Lemma t_update_empty: forall (T: Type) i q,
  (t_update (@empty T) i None) q = (@empty T) q.
Proof.
intros. unfold t_update. unfold empty.
destruct (beq_id i q).
- unfold t_empty. reflexivity.
- reflexivity.
Qed.

(*This one was added to preserve my sanity*)

Axiom t_update_empty_fext: forall (T: Type) i,
  t_update (@empty T) i None = @empty T.

Lemma adapt_empty: forall t,
  adapt empty t = t.
Proof. induction t; eauto; simpl.
- rewrite IHt1. rewrite IHt2. reflexivity.
- rewrite t_update_empty_fext. rewrite IHt. reflexivity.
- rewrite IHt1. rewrite IHt2. rewrite IHt3. reflexivity.
Qed.

Definition tm_context_closed (Sigma: tm_context): Prop :=
  forall i t, Sigma i = Some t -> closed t.

(*Note: You cannot use "closed" in this proof, this is
another example of proving more specific things being better*)
Lemma adapt_nonee: forall i s t,
  ~ appears_free_in i t -> [i := s] t = t.
Proof.
induction t; intros.
- simpl. remember (beq_id i i0) as b. symmetry in Heqb.
destruct b.
  + apply beq_id_true_iff in Heqb. subst.
  exfalso; apply H. apply afi_var.
  + auto.

- simpl. assert (~ appears_free_in i t1).
{ intro. apply H. apply afi_app1. auto. }
assert (~ appears_free_in i t2).
{ intro. apply H. apply afi_app2. auto. }

apply IHt1 in H0; apply IHt2 in H1.
rewrite H0; rewrite H1. auto.

- simpl. remember (beq_id i i0) as b.
symmetry in Heqb; destruct b.
  + (*i = i0*) auto.
  + apply beq_id_false_iff in Heqb.
  assert (~ appears_free_in i t0).
  { intro. apply H. apply afi_abs; auto. }

  apply IHt in H0. rewrite H0. auto.

- simpl; auto.
- simpl. reflexivity.
- simpl. assert (~ appears_free_in i t1).
{ intro. apply H. apply afi_if1. auto. }
assert (~ appears_free_in i t2).
{ intro. apply H. apply afi_if2. auto. }
assert (~ appears_free_in i t3).
{ intro. apply H. apply afi_if3. auto. }
apply IHt1 in H0; apply IHt2 in H1;
apply IHt3 in H2. rewrite H0; rewrite H1;
rewrite H2. auto.
Qed.

Corollary adapt_closed: forall i s t,
  closed t -> [i := s] t = t.
Proof.
intros. unfold closed in H.
apply adapt_nonee. apply H.
Qed.

Lemma adapt_correct: forall i s t Sigma,
  Sigma i = None -> tm_context_closed Sigma ->
  [i:=s] adapt Sigma t =
  adapt (t_update Sigma i (Some s)) t.
Proof.
induction t; intros.
- simpl. unfold t_update. remember (beq_id i i0) as b.
symmetry in Heqb. destruct b.
  + apply beq_id_true_iff in Heqb. subst.
  rewrite H. simpl. rewrite <- beq_id_refl. auto.
  + (*i <> i0*)
  remember (Sigma i0) as Si0. destruct Si0.
    * (*Sigma i0 = Some t*) apply adapt_closed.
    unfold tm_context_closed in H0. symmetry in HeqSi0.
    apply H0 in HeqSi0. auto.
    * simpl. rewrite Heqb. auto.

- simpl. remember H as H'. clear HeqH'.
apply IHt1 in H. Focus 2. auto. apply IHt2 in H0.
Focus 2. auto. rewrite H; rewrite H0. auto.

- simpl. remember (beq_id i i0) as b.
symmetry in Heqb. destruct b.
  + apply beq_id_true_iff in Heqb.
  subst. rewrite t_update_shadow. auto.
  + rewrite t_update_permute. Focus 2.
  apply beq_id_false_iff; auto.
  assert ([i := s] adapt (t_update Sigma i0 None) t0 =
    adapt (t_update (t_update Sigma i0 None) i (Some s)) t0).
  { apply IHt. unfold t_update.
  apply beq_id_false_iff in Heqb.
  assert (i0 <> i). { intro. apply Heqb. auto. }
  assert (beq_id i0 i = false). { apply beq_id_false_iff in H1.
  auto. } rewrite H2. auto.
  unfold tm_context_closed. intros. unfold t_update in H1.
  destruct (beq_id i0 i1).
    * inversion H1. * unfold tm_context_closed in H0.
    eapply H0. eauto. }

  rewrite H1; auto.

- simpl. auto.
- simpl. auto.
- simpl. assert ([i := s] adapt Sigma t1 =
  adapt (t_update Sigma i (Some s)) t1).
  { apply IHt1; auto. }
assert ([i := s] adapt Sigma t2 =
  adapt (t_update Sigma i (Some s)) t2).
  { apply IHt2; auto. }
assert ([i := s] adapt Sigma t3 =
  adapt (t_update Sigma i (Some s)) t3).
  { apply IHt3; auto. }

clear IHt1; clear IHt2; clear IHt3.
rewrite H1; rewrite H2; rewrite H3.
auto.
Qed.
(*adapt is correct!*)





Definition adapt_fit_context (Sigma: tm_context) (Gamma: context): Prop :=
  (forall i t,
    Sigma i = Some t ->
    value t /\ exists T, Gamma i = Some T /\ empty |- t \in T ) /\
  (forall i T,
    Gamma i = Some T ->
    exists t, Sigma i = Some t /\ empty |- t \in T /\
      value t).

(*all the adapt terms must be a value otherwise the proof will be stunned on t_var*)
(*all the adapt terms must be well_typed in the empty context, and the type must be specified in the type context*)
(*the adapt context contains precisely those variables specified in the type context, and nothing else*)

Definition atom (t: tm): Prop :=
  t = ttrue \/ t = tfalse.

Theorem halt: forall t Gamma T Sigma,
  Gamma |- t \in T ->
  adapt_fit_context Sigma Gamma ->
  (normalizing atom (adapt Sigma t)) \/
  (exists i T1 u, t ==>* tabs i T1 u /\
    forall s, empty |- s \in T1 -> value s ->
    normalizing atom (adapt (t_update Sigma i (Some s)) u)).
Proof.
induction t; intros.
- left. inversion H0. simpl.
remember (Sigma i) as si eqn:Hsi.
symmetry in Hsi. destruct si.
  + apply H1 in Hsi. destruct Hsi. unfold normalizing.
  exists t. split; auto. destruct H3.




(** [] *)

End STLCArith.

(** $Date: 2016-12-20 12:03:19 -0500 (Tue, 20 Dec 2016) $ *)














