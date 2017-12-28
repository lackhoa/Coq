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

Lemma value_typable_empty: forall t,
  value t -> exists T, empty |- t \in T.
  Proof.
  induction t; intros.
  - inversion H. - inversion H.
  - Abort.

Lemma app_multi_step_1 : forall t1 t2 t1',
  t1 ==>* t1' ->
  tapp t1 t2 ==>* tapp t1' t2.
Proof. intros. generalize dependent t2. induction H.
- eauto.
- rename x0 into x; rename y0 into y; rename z0 into z.
intros. assert (tapp x t2 ==> tapp y t2).
{ apply ST_App1. assumption. }

eapply multi_step; eauto.
Qed.

Lemma app_multi_step_2 : forall v1 t2 t2',
  t2 ==>* t2' -> value v1 ->
  tapp v1 t2 ==>* tapp v1 t2'.
Proof. intros. generalize dependent v1. induction H.
- eauto.
- rename x0 into x; rename y0 into y; rename z0 into z.
intros. assert (tapp v1 x ==> tapp v1 y).
{ apply ST_App2; assumption. }

eapply multi_step; eauto.
Qed.

Theorem app_multi_step : forall t1 t1' t2 t2',
  t1 ==>* t1' -> value t1' -> t2 ==>* t2'->
  tapp t1 t2 ==>* tapp t1' t2'.
Proof.
intros. induction H.
- apply app_multi_step_2; assumption.
- apply IHmulti in H0. clear IHmulti.
assert (tapp x0 t2 ==> tapp y0 t2).
{ apply ST_App1; assumption. }
eapply multi_step; eauto.
Qed.

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

Definition atom (t: tm): Prop :=
  t = ttrue \/ t = tfalse.




Definition value_core (t: tm): Prop :=
  atom t \/
  (exists i T1 u, t = tabs i T1 u /\
  (forall s, value s -> empty |- s \in T1 ->
    normalizing value ([i:=s] u))).







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

Lemma adapt_fit_context_closed: forall Gamma Sigma,
  adapt_fit_context Sigma Gamma -> tm_context_closed Sigma.
  Proof.
  intros. unfold tm_context_closed. intros.
  inversion H. apply H1 in H0.
  destruct H0. destruct H3. destruct H3.
  eapply typable_empty__closed. eauto.
  Qed.

Lemma adapt_fit_context_lost: forall Gamma Sigma i,
  adapt_fit_context Sigma Gamma ->
  adapt_fit_context (t_update Sigma i None) (t_update Gamma i None).
  Proof.
  intros. inversion H. unfold adapt_fit_context.
  clear H. split.
  - intros. unfold t_update in *.
  destruct (beq_id i i0).
    + inversion H. + apply H0; auto.
  - intros. unfold t_update in *.
  destruct (beq_id i i0).
    + inversion H. + apply H1; auto.
  Qed.

Lemma adapt_fit_context_gain: forall Gamma Sigma i t T,
  adapt_fit_context Sigma Gamma ->
  empty |- t \in T -> value t ->
  adapt_fit_context (t_update Sigma i (Some t)) (t_update Gamma i (Some T)).
  Proof.
  intros. inversion H. unfold adapt_fit_context.
  split; intros.
  - unfold t_update in *. destruct (beq_id i i0).
    + inversion H4; subst. split; auto. eauto.
    + apply H2; auto.
  - unfold t_update in *. destruct (beq_id i i0).
    + inversion H4; subst. eauto.
    + apply H3; auto.
  Qed.
  
Theorem adapt_pres_typing: forall Gamma Sigma t T,
  Gamma |- t \in T ->
  adapt_fit_context Sigma Gamma ->
  empty |- (adapt Sigma t) \in T.
  Proof.
  induction Sigma; intros.
  - 
  
  
  intros Gamma Sigma t. generalize dependent Gamma.
  generalize dependent Sigma. induction t; intros.
  - inversion H; subst. simpl.
  inversion H0. apply H2 in H3. destruct H3.
  destruct H3. rewrite H3. destruct H4; auto.
  - simpl. inversion H; subst. eapply T_App.
  eapply IHt1; eauto. eapply IHt2; eauto.
  - simpl. inversion H; subst. eapply T_Abs.
  rename t into T. 

(*==================Prime=====================*)
(*This is my effort to break the abstraction wall, as you can see, it failed!*)
Inductive Prime: tm -> Prop :=
  | PVar: forall x, Prime (tvar x)
  | PAbs: forall i T u, Prime (tabs i T u)
  | PApp: forall t1 t2 i T1, Prime t1 -> Prime t2 ->
    Prime (tapp (tabs i T1 t1) t2)

  | PTrue: Prime ttrue
  | PFalse: Prime tfalse
  | PIf: forall t1 t2 t3, Prime (tif t1 t2 t3).

Theorem hatl_prime: forall t Gamma T Sigma,
  Prime t -> Gamma |- t \in T ->
  adapt_fit_context Sigma Gamma ->
  normalizing value (adapt Sigma t).
  Proof.
  intros. generalize dependent Gamma;
  generalize dependent Sigma;
  generalize dependent T.
   induction H; intros.
  - inversion H1. inversion H0; subst.
  apply H2 in H5. simpl. destruct H5.
  destruct H3. rewrite H3. destruct H4.
  unfold normalizing. eauto.

  - simpl. unfold normalizing.
  exists (tabs i T (adapt (t_update Sigma i None) u));
  eauto.

  - simpl. inversion H1; subst. inversion H2.
  assert (normalizing value (adapt Sigma t2)).
  { eapply IHPrime2; eauto. }
  destruct H5. destruct H5.
  assert (tapp (tabs i T1 (adapt (t_update Sigma i None) t1)) (adapt Sigma t2) ==>* tapp (tabs i T1 (adapt (t_update Sigma i None) t1)) x0).
  { apply app_multi_step_2; auto. }
  
  clear IHPrime2.
  
  assert (tapp (tabs i T1 (adapt (t_update Sigma i None) t1)) x0 ==> [i := x0]adapt (t_update Sigma i None) t1).
  { apply ST_AppAbs; auto. }
  
  assert (normalizing value ([i := x0] adapt (t_update Sigma i None) t1)).
  { assert ([i := x0] adapt (t_update Sigma i None) t1 = adapt (t_update (t_update Sigma i None) i (Some x0)) t1). { apply adapt_correct; auto. apply t_update_eq.
  apply adapt_fit_context_closed with (t_update Gamma i None). apply adapt_fit_context_lost. auto. }
  rewrite H11. eapply IHPrime1. inversion H6; subst.
  eauto. rewrite t_update_shadow. apply adapt_fit_context_gain; auto. inversion H6; subst.
   }













(** [] *)

End STLCArith.

(** $Date: 2016-12-20 12:03:19 -0500 (Tue, 20 Dec 2016) $ *)














