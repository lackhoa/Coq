(** * StlcProp: Properties of STLC *)

Require Import Maps.
Require Import Types.
Require Import Stlc.
Require Import Smallstep.
Module STLCProp.
Import STLC.

(** In this chapter, we develop the fundamental theory of the Simply
    Typed Lambda Calculus -- in particular, the type safety
    theorem. *)

(* ################################################################# *)
(** * Canonical Forms *)

(** As we saw for the simple calculus in the [Types] chapter, the
    first step in establishing basic properties of reduction and types
    is to identify the possible _canonical forms_ (i.e., well-typed
    closed values) belonging to each type.  For [Bool], these are the boolean
    values [ttrue] and [tfalse].  For arrow types, the canonical forms
    are lambda-abstractions.  *)

Lemma canonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0. exists t0.  auto.
Qed.

(* ################################################################# *)
(** * Progress *)

(** The _progress_ theorem tells us that closed, well-typed
    terms are not stuck: either a well-typed term is a value, or it
    can take a reduction step.  The proof is a relatively
    straightforward extension of the progress proof we saw in the
    [Types] chapter.  We'll give the proof in English first, then
    the formal version. *)

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

(** _Proof_: By induction on the derivation of [|- t \in T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we can see by inspecting the rule that [t]
      is a value.

    - If the last rule of the derivation is [T_App], then [t] has the
      form [t1 t2] for some [t1] and [t2], where [|- t1 \in T2 -> T]
      and [|- t2 \in T2] for some type [T2].  By the induction
      hypothesis, either [t1] is a value or it can take a reduction
      step.

        - If [t1] is a value, then consider [t2], which by the other
          induction hypothesis must also either be a value or take a
          step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation is [T_If], then [t = if t1
      then t2 else t3], where [t1] has type [Bool].  By the IH, [t1]
      either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps
          to [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]). *)
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  induction Ht; subst Gamma...
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    inversion H.

  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        assert (exists x0 t0, t1 = tabs x0 T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...

      * (* t2 steps *)
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...

    + (* t1 steps *)
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  - (* T_If *)
    right. destruct IHHt1...

    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.

    + (* t1 also steps *)
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...
Qed.

(** **** Exercise: 3 stars, advanced (progress_from_term_ind)  *)
(** Show that progress can also be proved by induction on terms
    instead of induction on typing derivations. *)

Theorem progress_tapp : forall T t1 t2,
  empty |- (tapp t1 t2) \in T ->
  (value t1 \/ exists t1', t1 ==> t1') ->
  (value t2 \/ exists t2', t2 ==> t2') ->
  exists t', tapp t1 t2 ==> t'.
Proof. intros. destruct H0.
- rename t1 into v1. destruct H1.
  + (*Both are values*) inversion H0; subst.
    * exists ([x0 := t2] t). apply ST_AppAbs; assumption.
    * inversion H; subst. inversion H5.
    * inversion H. inversion H5.
  + (*v1 value, t2 step*) destruct H1 as [t2']. exists (tapp v1 t2').
  apply ST_App2; assumption.
- destruct H0 as [t1']. exists (tapp t1' t2). apply ST_App1; assumption.
Qed.


Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof.
intros t.
induction t; intros T Ht; auto.
- inversion Ht; subst. inversion H1.
- inversion Ht; subst. right. remember H2 as H2'.
remember H4 as H4'. clear HeqH2'; clear HeqH4'.
apply IHt1 in H2; apply IHt2 in H4; subst.
clear IHt1; clear IHt2. (*Already did this part*)
eapply progress_tapp; eauto.

- right. inversion Ht; subst; clear Ht. inversion H3; subst; clear H3.
  + inversion H. + assert (empty |- tapp t0 t4 \in TBool).
  { eapply T_App; eauto. } apply IHt1 in H1.
  destruct H1. inversion H1. (*Final blow*)
  destruct H1. exists (tif x0 t2 t3); apply ST_If; auto.
  + exists t2. apply ST_IfTrue; auto.
  + exists t3; apply ST_IfFalse; auto.
  + assert (empty |- (tif t0 t4 t5) \in TBool).
   { apply T_If; auto. }
  apply IHt1 in H2. destruct H2. * inversion H2.
  * destruct H2 as [t'']. exists (tif t'' t2 t3).
  apply ST_If. auto. Qed.


(** [] *)

(* ################################################################# *)
(** * Preservation *)

(** The other half of the type soundness property is the
    preservation of types during reduction.  For this part, we'll need
    to develop some technical machinery for reasoning about variables
    and substitution.  Working from top to bottom (from the high-level
    property we are actually interested in to the lowest-level
    technical lemmas that are needed by various cases of the more
    interesting proofs), the story goes like this:

      - The _preservation theorem_ is proved by induction on a typing
        derivation, pretty much as we did in the [Types] chapter.
        The one case that is significantly different is the one for
        the [ST_AppAbs] rule, whose definition uses the substitution
        operation.  To see that this step preserves typing, we need to
        know that the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed)
        term [s] for a variable [x] in a term [t] preserves the type
        of [t].  The proof goes by induction on the form of [t] and
        requires looking at all the different cases in the definition
        of substitition.  This time, the tricky cases are the ones for
        variables and for function abstractions.  In both, we discover
        that we need to take a term [s] that has been shown to be
        well-typed in some context [Gamma] and consider the same term
        [s] in a slightly different context [Gamma'].  For this we
        prove a...

      - _context invariance_ lemma, showing that typing is preserved
        under "inessential changes" to the context [Gamma] -- in
        particular, changes that do not affect any of the free
        variables of the term.  And finally, for this, we need a
        careful definition of...

      - the _free variables_ of a term -- i.e., those variables
        mentioned in a term and not in the scope of an enclosing
        function abstraction binding a variable of the same name.

   To make Coq happy, we need to formalize the story in the opposite
   order... *)

(* ================================================================= *)
(** ** Free Occurrences *)

(** A variable [x] _appears free in_ a term _t_ if [t] contains some
    occurrence of [x] that is not under an abstraction labeled [x].
    For example:
      - [y] appears free, but [x] does not, in [\x:T->U. x y]
      - both [x] and [y] appear free in [(\x:T->U. x y) x]
      - no variables appear free in [\x:T->U. \y:T. x y]

    Formally: *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif t1 t2 t3).

Hint Constructors appears_free_in.

(** The _free variables_ of a term are just the variables that appear
    free in it.  A term with no free variables is said to be
    _closed_. *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(** An _open_ term is one that is not closed (or not known to be
    closed). *)

(** **** Exercise: 1 starM (afi)  *)
(** In the space below, write out the rules of the [appears_free_in]
    relation in informal inference-rule notation.  (Use whatever
    notational conventions you like -- the point of the exercise is
    just for you to think a bit about the meaning of each rule.)
    Although this is a rather low-level, technical definition,
    understanding it is crucial to understanding substitution and its
    properties, which are really the crux of the lambda-calculus. *)

(*
        afi_var:
        (nothing)
        ----------
        afi x (tvar x)
        
        afi_app1:
        afi x t1
        ---------------------
        afi x (tapp t1 t2)
        
        afi_app2:
        afi x t2
        ------------------------
        afi x (tapp t1 t2)
        
        afi_abs:
        afi x t
        x <> y
        -------------------------
        afi x (tabs y T t)

        blah... blah... blah...

*)
(** [] *)

(* ================================================================= *)
(** ** Substitution *)

(** To prove that substitution preserves typing, we first need a
    technical lemma connecting free variables and typing contexts: If
    a variable [x] appears free in a term [t], and if we know [t] is
    well typed in context [Gamma], then it must be the case that
    [Gamma] assigns a type to [x]. *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.

(** _Proof_: We show, by induction on the proof that [x] appears free
      in [t], that, for all contexts [Gamma], if [t] is well typed
      under [Gamma], then [Gamma] assigns some type to [x].

      - If the last rule used is [afi_var], then [t = x], and from the
        assumption that [t] is well typed under [Gamma] we have
        immediately that [Gamma] assigns a type to [x].

      - If the last rule used is [afi_app1], then [t = t1 t2] and [x]
        appears free in [t1].  Since [t] is well typed under [Gamma],
        we can see from the typing rules that [t1] must also be, and
        the IH then tells us that [Gamma] assigns [x] a type.

      - Almost all the other cases are similar: [x] appears free in a
        subterm of [t], and since [t] is well typed under [Gamma], we
        know the subterm of [t] in which [x] appears is well typed
        under [Gamma] as well, and the IH gives us exactly the
        conclusion we want.

      - The only remaining case is [afi_abs].  In this case [t =
        \y:T11.t12] and [x] appears free in [t12], and we also know
        that [x] is different from [y].  The difference from the
        previous cases is that, whereas [t] is well typed under
        [Gamma], its body [t12] is well typed under [(Gamma, y:T11)],
        so the IH allows us to conclude that [x] is assigned some type
        by the extended context [(Gamma, y:T11)].  To conclude that
        [Gamma] assigns a type to [x], we appeal to lemma
        [update_neq], noting that [x] and [y] are different
        variables. *)

Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H;
         intros; try solve [inversion H0; eauto].
  - (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite update_neq in H7; assumption.
Qed.

(** Next, we'll need the fact that any term [t] that is well typed in
    the empty context is closed (it has no free variables). *)

(** **** Exercise: 2 stars, optional (typable_empty__closed)  *)
Corollary typable_empty__closed : forall t T,
    empty |- t \in T  ->
    closed t.
Proof. intros t T H. intro x. intro.
assert (exists T': ty, empty x = Some T').
{ eapply free_in_context; eauto. }
inversion H1. inversion H2. Qed.


(** [] *)

(** Sometimes, when we have a proof [Gamma |- t : T], we will need to
    replace [Gamma] by a different context [Gamma'].  When is it safe
    to do this?  Intuitively, it must at least be the case that
    [Gamma'] assigns the same types as [Gamma] to all the variables
    that appear free in [t]. In fact, this is the only condition that
    is needed. *)

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.

(** _Proof_: By induction on the derivation of 
    [Gamma |- t \in T].

      - If the last rule in the derivation was [T_Var], then [t = x]
        and [Gamma x = T].  By assumption, [Gamma' x = T] as well, and
        hence [Gamma' |- t \in T] by [T_Var].

      - If the last rule was [T_Abs], then [t = \y:T11. t12], with [T
        = T11 -> T12] and [Gamma, y:T11 |- t12 \in T12].  The
        induction hypothesis is that, for any context [Gamma''], if
        [Gamma, y:T11] and [Gamma''] assign the same types to all the
        free variables in [t12], then [t12] has type [T12] under
        [Gamma''].  Let [Gamma'] be a context which agrees with
        [Gamma] on the free variables in [t]; we must show [Gamma' |-
        \y:T11. t12 \in T11 -> T12].

        By [T_Abs], it suffices to show that [Gamma', y:T11 |- t12 \in
        T12].  By the IH (setting [Gamma'' = Gamma', y:T11]), it
        suffices to show that [Gamma, y:T11] and [Gamma', y:T11] agree
        on all the variables that appear free in [t12].

        Any variable occurring free in [t12] must be either [y] or
        some other variable.  [Gamma, y:T11] and [Gamma', y:T11]
        clearly agree on [y].  Otherwise, note that any variable other
        than [y] that occurs free in [t12] also occurs free in [t =
        \y:T11. t12], and by assumption [Gamma] and [Gamma'] agree on
        all such variables; hence so do [Gamma, y:T11] and [Gamma',
        y:T11].

      - If the last rule was [T_App], then [t = t1 t2], with [Gamma |-
        t1 \in T2 -> T] and [Gamma |- t2 \in T2].  One induction
        hypothesis states that for all contexts [Gamma'], if [Gamma']
        agrees with [Gamma] on the free variables in [t1], then [t1]
        has type [T2 -> T] under [Gamma']; there is a similar IH for
        [t2].  We must show that [t1 t2] also has type [T] under
        [Gamma'], given the assumption that [Gamma'] agrees with
        [Gamma] on all the free variables in [t1 t2].  By [T_App], it
        suffices to show that [t1] and [t2] each have the same type
        under [Gamma'] as under [Gamma].  But all free variables in
        [t1] are also free in [t1 t2], and similarly for [t2]; hence
        the desired result follows from the induction hypotheses. *)

Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros; auto.
  - (* T_Var *)
    apply T_Var. rewrite <- H0...
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to
       instantiate is [update Gamma x T11] *)
    unfold update. unfold t_update.
    destruct (beq_id x0 x1) eqn: Hx0x1...
    rewrite beq_id_false_iff in Hx0x1. apply H0.
    apply afi_abs; auto.
  - (* T_App *)
    apply T_App with T11... (*Why is it so easy? Because the type is
    already determined when you say that an application is well-typed*)
Qed.

(** Now we come to the conceptual heart of the proof that reduction
    preserves types -- namely, the observation that _substitution_
    preserves types. *)

(** Formally, the so-called _substitution lemma_ says this:
    Suppose we have a term [t] with a free variable [x], and suppose
    we've assigned a type [T] to [t] under the assumption that [x] has
    some type [U].  Also, suppose that we have some other term [v] and
    that we've shown that [v] has type [U].  Then, since [v] satisfies
    the assumption we made about [x] when typing [t], we can
    substitute [v] for each of the occurrences of [x] in [t] and
    obtain a new term that still has type [T]. *)

(** _Lemma_: If [Gamma,x:U |- t \in T] and [|- v \in U], then [Gamma |-
    [x:=v]t \in T]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     update Gamma x U |- t \in T ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in T.

(** One technical subtlety in the statement of the lemma is that
    we assign [v] the type [U] in the _empty_ context -- in other
    words, we assume [v] is closed.  This assumption considerably
    simplifies the [T_Abs] case of the proof (compared to assuming
    [Gamma |- v \in U], which would be the other reasonable assumption
    at this point) because the context invariance lemma then tells us
    that [v] has type [U] in any context at all -- we don't have to
    worry about free variables in [v] clashing with the variable being
    introduced into the context by [T_Abs].

    The substitution lemma can be viewed as a kind of commutation
    property.  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [x:=v] t ] -- the result is the same either
    way.

    _Proof_: We show, by induction on [t], that for all [T] and
    [Gamma], if [Gamma,x:U |- t \in T] and [|- v \in U], then [Gamma
    |- [x:=v]t \in T].

      - If [t] is a variable there are two cases to consider,
        depending on whether [t] is [x] or some other variable.

          - If [t = x], then from the fact that [Gamma, x:U |- x \in
            T] we conclude that [U = T].  We must show that [[x:=v]x =
            v] has type [T] under [Gamma], given the assumption that
            [v] has type [U = T] under the empty context.  This
            follows from context invariance: if a closed term has type
            [T] in the empty context, it has that type in any context.

          - If [t] is some variable [y] that is not equal to [x], then
            we need only note that [y] has the same type under [Gamma,
            x:U] as under [Gamma].

      - If [t] is an abstraction [\y:T11. t12], then the IH tells us,
        for all [Gamma'] and [T'], that if [Gamma',x:U |- t12 \in T']
        and [|- v \in U], then [Gamma' |- [x:=v]t12 \in T'].

        The substitution in the conclusion behaves differently
        depending on whether [x] and [y] are the same variable.

        First, suppose [x = y].  Then, by the definition of
        substitution, [[x:=v]t = t], so we just need to show [Gamma |-
        t \in T].  But we know [Gamma,x:U |- t : T], and, since [y]
        does not appear free in [\y:T11. t12], the context invariance
        lemma yields [Gamma |- t \in T].

        Second, suppose [x <> y].  We know [Gamma,x:U,y:T11 |- t12 \in
        T12] by inversion of the typing relation, from which
        [Gamma,y:T11,x:U |- t12 \in T12] follows by the context
        invariance lemma, so the IH applies, giving us [Gamma,y:T11 |-
        [x:=v]t12 \in T12].  By [T_Abs], [Gamma |- \y:T11. [x:=v]t12
        \in T11->T12], and by the definition of substitution (noting
        that [x <> y]), [Gamma |- \y:T11. [x:=v]t12 \in T11->T12] as
        required.

      - If [t] is an application [t1 t2], the result follows
        straightforwardly from the definition of substitution and the
        induction hypotheses.

      - The remaining cases are similar to the application case.

    _Technical note_: This proof is a rare case where an
    induction on terms, rather than typing derivations, yields a
    simpler argument.  The reason for this is that the assumption
    [update Gamma x U |- t \in T] is not completely generic, in the
    sense that one of the "slots" in the typing relation -- namely the
    context -- is not just a variable, and this means that Coq's
    native induction tactic does not give us the induction hypothesis
    that we want.  It is possible to work around this, but the needed
    generalization is a little tricky.  The term [t], on the other
    hand, is completely generic. 
*)

Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  - (* tvar *)
    rename i into y. destruct (beq_idP x y) as [Hxy|Hxy].
    + (* x=y *)
      subst.
      rewrite update_eq in H2.
      inversion H2; subst. 
      eapply context_invariance. eassumption.
      apply typable_empty__closed in Ht'. unfold closed in Ht'.
      intros.  apply (Ht' x0) in H0. inversion H0.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2...
  - (* tabs *)
    rename i into y. rename t into T. apply T_Abs.
    destruct (beq_idP x y) as [Hxy | Hxy].
    + (* x=y *)
      subst. rewrite update_shadow in H5. apply H5.
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (beq_idP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- beq_id_false_iff in Hxy.
      rewrite Hxy...
Qed.

(* ================================================================= *)
(** ** Main Theorem *)

(** We now have the tools we need to prove preservation: if a closed
    term [t] has type [T] and takes a step to [t'], then [t']
    is also a closed term with type [T].  In other words, the small-step
    reduction relation preserves types. *)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.

(** _Proof_: By induction on the derivation of [|- t \in T].

    - We can immediately rule out [T_Var], [T_Abs], [T_True], and
      [T_False] as the final rules in the derivation, since in each of
      these cases [t] cannot take a step.

    - If the last rule in the derivation is [T_App], then [t = t1
      t2].  There are three cases to consider, one for each rule that
      could be used to show that [t1 t2] takes a step to [t'].

        - If [t1 t2] takes a step by [ST_App1], with [t1] stepping to
          [t1'], then by the IH [t1'] has the same type as [t1], and
          hence [t1' t2] has the same type as [t1 t2].

        - The [ST_App2] case is similar.

        - If [t1 t2] takes a step by [ST_AppAbs], then [t1 =
          \x:T11.t12] and [t1 t2] steps to [[x:=t2]t12]; the
          desired result now follows from the fact that substitution
          preserves types.

    - If the last rule in the derivation is [T_If], then [t = if t1
      then t2 else t3], and there are again three cases depending on
      how [t] steps.

        - If [t] steps to [t2] or [t3], the result is immediate, since
          [t2] and [t3] have the same type as [t].

        - Otherwise, [t] steps by [ST_If], and the desired conclusion
          follows directly from the induction hypothesis. *)

Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Gamma; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.

(** **** Exercise: 2 stars, recommendedM (subject_expansion_stlc)  *)
(** An exercise in the [Types] chapter asked about the _subject
    expansion_ property for the simple language of arithmetic and
    boolean expressions.  Does this property hold for STLC?  That is,
    is it always the case that, if [t ==> t'] and [has_type t' T],
    then [empty |- t \in T]?  If so, prove it.  If not, give a
    counter-example not involving conditionals.

(* FILL IN HERE *)
[]
*)

(* ################################################################# *)
(** * Type Soundness *)

(** **** Exercise: 2 stars, optional (type_soundness)  *)
(** Put progress and preservation together and show that a well-typed
    term can _never_ reach a stuck state.  *)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti; rename x0 into t.
  - assert (value t \/ (exists t' : tm, t ==> t')).
  { eapply progress. eauto. }
  destruct H; auto.
  
  - rename y0 into t'. rename z0 into t''.
  (*Even if we shorten the multi-step chain, the proof wouldn't change*)
  apply IHHmulti.
    + eapply preservation; eauto.
    + eauto. + eauto. Qed.

(** [] *)

(* ################################################################# *)
(** * Uniqueness of Types *)

(** **** Exercise: 3 starsM (types_unique)  *)
(** Another nice property of the STLC is that types are unique: a
    given term (in a given context) has at most one type. *)
(** Formalize this statement and prove it. *)

Theorem types_unique:
  forall (t: tm) (Gamma : id -> option ty) (T1 T2: ty),
  Gamma |- t \in T1 ->
  Gamma |- t \in T2 ->
  T1 = T2.
Proof. intros t Gamma T1 T2 H1. generalize dependent T2.
induction H1; intros.
- inversion H0; subst. rewrite H in H3. inversion H3; auto.
- rename x0 into t. inversion H; subst.
  apply IHhas_type in H6. rewrite H6; auto.
- inversion H; subst. apply IHhas_type1 in H3.
  inversion H3. reflexivity.
- inversion H. reflexivity. - inversion H; reflexivity.
- inversion H; auto. Qed.

(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 1 starM (progress_preservation_statement)  *)
(** Without peeking at their statements above, write down the progress
    and preservation theorems for the simply typed lambda-calculus (as 
    Coq theorems). *) 

Definition khoa_progress: forall (t: tm) (T: ty),
  empty |- t \in T ->
  value t \/ (exists t', t ==> t') := progress.
  
Definition khoa_preservation : forall (t t': tm) (T: ty),
  empty |- t \in T ->
  t ==> t' ->
  empty |- t' \in T := preservation.

(** [] *)

(** **** Exercise: 2 starsM (stlc_variation1)  *)
(** Suppose we add a new term [zap] with the following reduction rule

                         ---------                  (ST_Zap)
                         t ==> zap

and the following typing rule:

                      ----------------               (T_Zap)
                      Gamma |- zap : T

    Which of the following properties of the STLC remain true in
    the presence of these rules?  For each property, write either
    "remains true" or "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* becomes false: everything can either be reduced to zap or the term 
that it would have been reduced to weren't it for zap *)
      - Progress
(* remains true (everything can be zap, which can always be reduced to itself)*)
      - Preservation
(* remains true: zap doesn't change your type, baby! *)
[]
*)

(** **** Exercise: 2 starsM (stlc_variation2)  *)
(** Suppose instead that we add a new term [foo] with the following 
    reduction rules:

                       -----------------                (ST_Foo1)
                       (\x:A. x) ==> foo

                         ------------                   (ST_Foo2)
                         foo ==> true

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* becomes false: obvious it fucks up abstraction *)
      - Progress
(* remains true *)
      - Preservation
(* becomes false: foo ==> true? GTFO! *)
[]
*)

(** **** Exercise: 2 starsM (stlc_variation3)  *)
(** Suppose instead that we remove the rule [ST_App1] from the [step]
    relation. Which of the following properties of the STLC remain
    true in the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* remains true *)
      - Progress
(* becomes false: if t1 can't make a step, what can we do? *)
      - Preservation
(* remains true: the type doesn't get messed up *)
[]
*)

(** **** Exercise: 2 stars, optional (stlc_variation4)  *)
(** Suppose instead that we add the following new rule to the 
    reduction relation:

            ----------------------------------        (ST_FunnyIfTrue)
            (if true then t1 else t2) ==> true

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* becomes false: obviously *)
      - Progress
(* remains true: true isn't that bad of a destination *)
      - Preservation
(* becomes false: the type of t1 and t2 get thrown out the window *)
[]
*)

(** **** Exercise: 2 stars, optional (stlc_variation5)  *)
(** Suppose instead that we add the following new rule to the typing 
    relation:

                 Gamma |- t1 \in Bool->Bool->Bool
                     Gamma |- t2 \in Bool
                 ------------------------------          (T_FunnyApp)
                    Gamma |- t1 t2 \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* remains true: only the typing is affected *)
      - Progress
(* becomes false: t1 t2 is not a value, but its type prevents it from
stepping anywhere, so... it's stuck *)
      - Preservation
(* becomes false: obviously *)
[]
*)

(** **** Exercise: 2 stars, optional (stlc_variation6)  *)
(** Suppose instead that we add the following new rule to the typing 
    relation:

                     Gamma |- t1 \in Bool
                     Gamma |- t2 \in Bool
                    ---------------------               (T_FunnyApp')
                    Gamma |- t1 t2 \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* remains true *)
      - Progress
(* becomes false: wtf can (t1 t2) be? They aren't value, where can they go? *)
      - Preservation
(* remains true: obviously t1 and t2 can't just be "glued" together to make
t1 and t2, no harm can be done *)
[]
*)

(** **** Exercise: 2 stars, optional (stlc_variation7)  *)
(** Suppose we add the following new rule to the typing relation 
    of the STLC:

                         ------------------- (T_FunnyAbs)
                         |- \x:Bool.t \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* remains true: no harm being done to step *)
      - Progress
(* becomes false: [\x:Bool. t] can't go anywhere *)
      - Preservation
(* remains true: same as determinism *)
[]
*)

End STLCProp.

(* ================================================================= *)
(** ** Exercise: STLC with Arithmetic *)

(** To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)

Module STLCArith.
Import STLC.

(** To types, we add a base type of natural numbers (and remove
    booleans, for brevity). *)

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat   : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing. *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tnat  : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm.

(** **** Exercise: 4 starsM (stlc_arith)  *)
(** Finish formalizing the definition and properties of the STLC
    extended with arithmetic.  Specifically:

    - Copy the core definitions and theorems for STLC that we went
      through above (from the definition of values through the
      Preservation theorem, inclusive), and paste it into the file at
      this point.  Do not copy examples, exercises, etc.  (In
      particular, make sure you don't copy any of the [] comments at
      the end of exercises, to avoid confusing the autograder.)

    - Extend the definitions of the [subst] operation and the [step]
      relation to include appropriate clauses for the arithmetic
      operators.

    - Extend the proofs of all the properties (up to [preservation])
      of the original STLC to deal with the new syntactic forms.  Make
      sure Coq accepts the whole file. *)

Inductive value : tm -> Prop :=
  | v_abs: forall x T t, value (tabs x T t)
  | v_nat: forall n, value (tnat n).
  
Hint Constructors value.

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if beq_id x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if beq_id x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)
  | tnat n => tnat n
  | tsucc t' => tsucc ([x:=s] t')
  | tpred t' => tpred ([x:=s] t')
  | tmult t1 t2 => tmult ([x:=s] t1) ([x:=s] t2)
  | tif0 t1 t2 t3 => tif0 ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end
where "'[' x ':=' s ']' t" := (subst x s t).

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tapp v1 t2 ==> tapp v1  t2'

  | ST_Succ : forall n,
    (tsucc (tnat n)) ==> (tnat (S n))
  | ST_Succ' : forall t t',
    t ==> t' ->
    (tsucc t) ==> (tsucc t')

  | ST_Pred : forall n,
    (tpred (tnat n)) ==> (tnat (pred n))
  | ST_Pred' : forall t t',
    t ==> t' ->
    (tpred t) ==> (tpred t')

  | ST_Mult : forall n1 n2,
    (tmult (tnat n1) (tnat n2)) ==> (tnat (n1 * n2))
  | ST_Mult'1 : forall t1 t1' t2,
    t1 ==> t1' ->
    (tmult t1 t2) ==> (tmult t1' t2)
  | ST_Mult'2 : forall v1 t2 t2', (*Note the order of reduction*)
    value v1 -> t2 ==> t2' ->
    (tmult v1 t2) ==> (tmult v1 t2')

  | ST_If0_True : forall n t2 t3,
    n = 0 ->
    (tif0 (tnat n) t2 t3) ==> t2
  | ST_If0_False : forall n t2 t3,
    n <> 0 ->
    (tif0 (tnat n) t2 t3) ==> t3
  | ST_If0 : forall t1 t1' t2 t3,
    t1 ==> t1' ->
    (tif0 t1 t2 t3) ==> (tif0 t1' t2 t3)
  
where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.
Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      update Gamma x T11 |- t12 \in T12 ->
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- tapp t1 t2 \in T12

  | T_Nat : forall n Gamma,
    Gamma |- tnat n \in TNat
  | T_Succ : forall t Gamma,
    Gamma |- t \in TNat ->
    Gamma |- tsucc t \in TNat
  | T_Pred : forall t Gamma,
    Gamma |- t \in TNat ->
    Gamma |- tpred t \in TNat
  | T_Mult : forall t1 t2 Gamma,
    Gamma |- t1 \in TNat ->
    Gamma |- t2 \in TNat ->
    Gamma |- tmult t1 t2 \in TNat
  | T_If0 : forall t1 t2 t3 T Gamma,
    Gamma |- t1 \in TNat ->
    Gamma |- t2 \in T ->
    Gamma |- t3 \in T ->
    Gamma |- tif0 t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Lemma canonical_forms_nat : forall t,
  empty |- t \in TNat ->
  value t ->
  exists n, (t = tnat n).
Proof.
  intros t Ht Hv. inversion Hv; subst. inversion Ht.
  eauto. Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0. exists t0.  auto.
Qed.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  induction Ht; subst Gamma...
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    inversion H.

  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        assert (exists x0 t0, t1 = tabs x0 T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...

      * (* t2 steps *)
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...

    + (* t1 steps *)
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  - right. assert (@empty ty = @empty ty) by reflexivity.
  apply IHHt in H; clear IHHt. destruct H.
    + assert (exists n, (t = tnat n)).
    { apply canonical_forms_nat; auto. }
    destruct H0 as [n]. exists (tnat (S n)).
    subst. apply ST_Succ.
    + destruct H. eauto.
  - right. assert (@empty ty = @empty ty) by reflexivity.
  apply IHHt in H; clear IHHt. destruct H.
    + assert (exists n, (t = tnat n)).
    { apply canonical_forms_nat; auto. }
    destruct H0 as [n]. exists (tnat (pred n)).
    subst. apply ST_Pred.
    + destruct H. eauto.
  - right. assert (@empty ty = @empty ty) by reflexivity.
  remember H as H'. clear HeqH'.
  apply IHHt1 in H; clear IHHt1.
  apply IHHt2 in H'; clear IHHt2.
  destruct H; destruct H'.
    + assert (exists n, (t1 = tnat n)).
    { apply canonical_forms_nat; auto. }
    assert (exists n, (t2 = tnat n)).
    { apply canonical_forms_nat; auto. }
    destruct H1 as [n1]. destruct H2 as [n2]. subst.
    exists (tnat (n1 * n2)). apply ST_Mult.
    + destruct H0. eauto. + destruct H. eauto.
    + destruct H; eauto.
  
  - right. assert (value t3 \/ (exists t' : tm, t3 ==> t')).
  auto. assert (value t2 \/ (exists t' : tm, t2 ==> t')). auto.
  assert (value t1 \/ (exists t' : tm, t1 ==> t')). auto.
  clear IHHt1; clear IHHt2; clear IHHt3. destruct H1.
    + assert (exists n, (t1 = tnat n)).
    { apply canonical_forms_nat; auto. }
    destruct H2 as [n]. subst. destruct n. eauto.
    exists t3. eapply ST_If0_False. auto.

    + destruct H1 as [t1']. eauto. Qed.

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_succ : forall x t,
      appears_free_in x t ->
      appears_free_in x (tsucc t)
  | afi_pred : forall x t,
      appears_free_in x t ->
      appears_free_in x (tpred t)
  | afi_mult1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tmult t1 t2)
  | afi_mult2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tmult t1 t2)
  | afi_if0_1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_if0_2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_if0_3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif0 t1 t2 t3).

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.

Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H;
         intros; try solve [inversion H0; eauto].
  - (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite update_neq in H7; assumption.
Qed.

Corollary typable_empty__closed : forall t T,
    empty |- t \in T  ->
    closed t.
Proof. intros t T H. intro x. intro.
assert (exists T': ty, empty x = Some T').
{ eapply free_in_context; eauto. }
inversion H1. inversion H2. Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros; auto.
  - (* T_Var *)
    apply T_Var. rewrite <- H0...
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to
       instantiate is [update Gamma x T11] *)
    unfold update. unfold t_update.
    destruct (beq_id x0 x1) eqn: Hx0x1...
    rewrite beq_id_false_iff in Hx0x1. apply H0.
    apply afi_abs; auto.
  - (* T_App *)
    apply T_App with T11...
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     update Gamma x U |- t \in T ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in T.
 Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  - (* tvar *)
    rename i into y. destruct (beq_idP x y) as [Hxy|Hxy].
    + (* x=y *)
      subst.
      rewrite update_eq in H2.
      inversion H2; subst. 
      eapply context_invariance. eassumption.
      apply typable_empty__closed in Ht'. unfold closed in Ht'.
      intros.  apply (Ht' x0) in H0. inversion H0.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2...
  - (* tabs *)
    rename i into y. rename t into T. apply T_Abs.
    destruct (beq_idP x y) as [Hxy | Hxy].
    + (* x=y *)
      subst. rewrite update_shadow in H5. apply H5.
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (beq_idP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- beq_id_false_iff in Hxy.
      rewrite Hxy...
Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Gamma; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Reserved Notation "t1 '==>' t2" (at level 40).

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti; rename x0 into t.
  - assert (value t \/ (exists t' : tm, t ==> t')).
  { eapply progress. eauto. }
  destruct H; auto.
  
  - rename y0 into t'. rename z0 into t''.
  (*Even if we shorten the multi-step chain, the proof wouldn't change*)
  apply IHHmulti.
    + eapply preservation; eauto.
    + eauto. + eauto.
Qed.

Theorem types_unique:
  forall (t: tm) (Gamma : id -> option ty) (T1 T2: ty),
  Gamma |- t \in T1 ->
  Gamma |- t \in T2 ->
  T1 = T2.
Proof. intros t Gamma T1 T2 H1. generalize dependent T2.
induction H1; intros.
- inversion H0; subst. rewrite H in H3. inversion H3; auto.
- rename x0 into t. inversion H; subst.
  apply IHhas_type in H6. rewrite H6; auto.
- inversion H; subst. apply IHhas_type1 in H3.
  inversion H3. reflexivity.
- inversion H. reflexivity. - inversion H; reflexivity.
- inversion H; auto. - inversion H; auto. - inversion H; auto.
Qed.

Lemma preservation_multi : forall t t' T,
     empty |- t \in T  ->
     t ==>* t'  ->
     empty |- t' \in T.
Proof. intros t t' T HType HMulti.
induction HMulti; intros.
- assumption.
- assert (empty |- y0 \in T). { eapply preservation; eauto. }
eapply IHHMulti; eauto. Qed.

(*This doesn't happen*)
(*Theorem deterministic : forall t t1 t2,
  t ==> t1 -> t ==> t2 -> t1 = t2.*)



(*Lemma let_it_out : forall t T11 T12,
  empty |- t \in TArrow T11 T12 ->
  exists t', t ==>* t' /\ value t'.
Proof. intro. induction t; intros.
- inversion H; subst. inversion H2.
- inversion H; subst. inversion H5.*)

(*Okay, so that's it!*)
(* But the question remains: does it halt?*)
Theorem halt : forall t T,
  empty |- t \in T ->
  exists t', value t' /\ t ==>* t'.
Proof.
(*Induction on t: There's nothing to
support application*)
(*intros t. induction t; intros.
- inversion H. inversion H2.
- inversion H; subst. rename T11 into T0.
remember H3 as Ht1. clear HeqHt1.
apply IHt1 in H3.
remember H5 as Ht2; clear HeqHt2.
apply IHt2 in H5.
destruct H3 as [t1']. destruct H5 as [t2'].
destruct H0; destruct H1. exists *)





(*Induction on type: Nothing to support from T
to TArrow T ..*)
(*intros t T. generalize dependent t.
induction T; intros.
- *)




(*Induction on has_type: again, what to do after
application? *)
intros t T HType. remember empty as Gamma.
induction HType; subst.
- inversion H.
- exists (tabs x0 T11 t12); eauto.
- assert (@empty ty = @empty ty) as fuck1; auto.
apply IHHType1 in fuck1; clear IHHType1.
assert (@empty ty = @empty ty) as fuck2; auto;
apply IHHType2 in fuck2; clear IHHType2.
destruct fuck1 as [t1']; destruct fuck2 as [t2'].
destruct H. destruct H.
  + destruct H0. exists ([x0:=t2'] t). rename x0 into x.
  assert (empty |- (tabs x T t) \in (TArrow T11 T12)).
  { eapply preservation_multi; eauto. }
  inversion H2; subst.

  assert (empty |- t2' \in T11). { eapply preservation_multi; eauto. }
  assert (empty |- [x := t2'] t \in T12).
  { eapply substitution_preserves_typing; eauto. }
Abort.

(*Number of appearance of a variable in a single term*)
Fixpoint appears_count (x : id) (t: tm) : nat :=
  match t with
  | tvar x' =>
      match beq_id x x' with
      | true => 1
      | false => 0
      end
  | tapp t1 t2 =>
      (appears_count x t1) + (appears_count x t2)
  | tabs x' T t1 =>
      match beq_id x x' with
        | true => 0 (*bound collision*)
        | false => appears_count x t1
        end
  | tnat _ => 0
  | tsucc t' => appears_count x t'
  | tpred t' => appears_count x t'
  | tmult t1 t2 =>
      (appears_count x t2) + (appears_count x t2)
  | tif0 t1 t2 t3 =>
      (appears_count x t1) + (appears_count x t2) +
        (appears_count x t3)
  end.

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

Lemma canonical_forms_serious : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  exists t' x u, t' = tabs x T1 u /\ t ==>* t'.
Proof. intros t. induction t; intros.
- (*tvar*) inversion H. subst. inversion H2.
- (*tapp*) inversion H; subst. apply IHt1 in H3.
destruct H3. destruct H0. destruct H0. destruct H0.
rename x0 into abs. rename x2 into t'.
Abort. (*t2 must be a value...*)

Theorem deterministic : forall t t1 t2,
  t ==> t1 -> t ==> t2 -> t1 = t2.
Proof. induction t; intros.
- inversion H.
- inversion H; inversion H0; subst.
  + inversion H5. reflexivity.
  + (*Impossibility: a value steps to somewhere?*)
  inversion H8.
  + inversion H4; subst. inversion H9. inversion H9.
  + inversion H4.
  + assert (t1' = t1'0) by (apply IHt1; auto). subst.
  reflexivity.
  + inversion H7; subst. inversion H4. inversion H4.
  + inversion H9; subst; inversion H5.
  + inversion H3; subst; inversion H9.
  + assert (t2' = t2'0) by (apply IHt2; assumption).
  subst. reflexivity.

- inversion H.
- inversion H.
- inversion H; inversion H0; subst.
  + inversion H4. reflexivity.
  + inversion H4. + inversion H2.
  + assert (t' = t'0) by (apply IHt; assumption);
  subst; reflexivity.

- inversion H; inversion H0; subst.
  + inversion H4. reflexivity.
  + inversion H4. + inversion H2.
  + assert (t' = t'0) by (apply IHt; assumption);
  subst; reflexivity.

- inversion H; inversion H0; subst.
  + inversion H5; inversion H6; subst; reflexivity.
  + inversion H7. + inversion H8. + inversion H4.
  + assert (t1' = t1'0) by (apply IHt1; assumption); subst.
  reflexivity.
  + inversion H7; subst; inversion H4.
  + inversion H5. + inversion H3; subst; inversion H9.
  + assert (t2' = t2'0) by (apply IHt2; assumption); subst.
  reflexivity.

- inversion H; inversion H0; subst; try auto.
  + destruct H10. inversion H6. reflexivity.
  + inversion H10. + inversion H6. destruct H5. auto.
  + inversion H10. + inversion H5. + inversion H5.
  + assert (t1' = t1'0) by (apply IHt1; assumption); subst.
  reflexivity.
Qed.

(*if we can prove that the complexity of a term always decrease
by one after every reduction step, we win!*)

Inductive complex: tm -> nat -> Prop :=
  | C_App: forall t1 t2 n1 n2 x T u,
    complex t1 n1 -> complex t2 n2 ->
    t1 ==>* (tabs x T u) ->
    complex (tapp t1 t2) (n1 + (appears_count x t1) * n2 + 1)

  | C_Abs: forall i T t n,
    complex t n ->
    complex (tabs i T t) n
  | C_Nat: forall n, complex (tnat n) 0
  | C_Succ: forall t n,
    complex t n ->
    complex (tsucc t) (n + 1)
  | C_Pred: forall t n,
    complex t n ->
    complex (tsucc t) (n + 1)
  | C_Mult: forall t1 t2 n1 n2,
    complex t1 n1 -> complex t2 n2 ->
    complex (tmult t1 t2) (n1 + n2 + 1)
  | C_If0_True: forall t1 t2 t3 n1 n2,
    complex t1 n1 -> complex t2 n2 ->
    tif0 t1 t2 t3 ==>* t2 ->
    complex (tif0 t1 t2 t3) (n1 + n2 + 1)
  | C_If0_False: forall t1 t2 t3 n1 n3,
    complex t1 n1 -> complex t3 n3 ->
    tif0 t1 t2 t3 ==>* t3 ->
    complex (tif0 t1 t2 t3) (n1 + n3 + 1).
(*This is the NEW HOPE: complexity theory*)

(*I initially used Fixpoint computation but 
it was just so inflexible for the tif0 case (guess what?
now I know what they were talking about when comparing
Fixpoint and Inductive properties, it takes a long time,
but it was worth it!*)

Lemma value_subst: forall x s t,
  value t -> value ([x := s] t).
Proof. intros. inversion H.
- simpl. destruct (beq_id x0 x1); apply v_abs.
- simpl. apply v_nat.
Qed.

Lemma subst_order: forall u x s t,
  [x := [x := s] t] u =
  [x := s] ([x := t] u).
Proof. intro u. induction u; intros.
- simpl. remember (beq_id x0 i) as b.
destruct b. reflexivity. simpl. rewrite <- Heqb.
reflexivity.
- simpl. assert ([x0 := [x0 := s] t] u1 = 
  [x0 := s] ([x0 := t] u1)) by (apply IHu1).
assert ([x0 := [x0 := s] t] u2 = 
  [x0 := s] ([x0 := t] u2)) by (apply IHu2).
rewrite H. rewrite H0. reflexivity.

- simpl. remember (beq_id x0 i) as b. destruct b.
reflexivity. assert ([x0 := [x0 := s] t0] u
  = [x0 := s] ([x0 := t0] u)) by (apply IHu).
rewrite H. reflexivity.

- simpl. reflexivity.
- simpl. assert ([x0 := [x0 := s] t] u =
  [x0 := s] ([x0 := t] u)) by (apply IHu).
rewrite H; reflexivity.
- simpl. assert ([x0 := [x0 := s] t] u =
  [x0 := s] ([x0 := t] u)) by (apply IHu).
rewrite H; reflexivity.
- simpl. assert ([x0 := [x0 := s] t] u1 =
  [x0 := s] ([x0 := t] u1)) by (apply IHu1).
assert ([x0 := [x0 := s] t] u2 =
  [x0 := s] ([x0 := t] u2)) by (apply IHu2).
rewrite H; rewrite H0; reflexivity.

- simpl. assert ([x0 := [x0 := s] t] u1 =
  [x0 := s] ([x0 := t] u1)) by (apply IHu1).
assert ([x0 := [x0 := s] t] u2 =
  [x0 := s] ([x0 := t] u2)) by (apply IHu2).
assert ([x0 := [x0 := s] t] u3 =
  [x0 := s] ([x0 := t] u3)) by (apply IHu3).
rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed. (*Didn't think it would work!*)

Lemma subst_order2: forall u x1 x0 s t,
  [x1 := [x0 := s] t] ([x0 := s] u) =
  [x0 := s] ([x1 := t] u).
Proof.
intro u; induction u; intros; simpl.
- remember (beq_id x0 i) as b0.
remember (beq_id x1 i) as b1.
destruct b0; destruct b1.
  + symmetry in Heqb0. apply beq_id_true_iff in Heqb0.
  symmetry in Heqb1. apply beq_id_true_iff in Heqb1.
  subst.

Theorem subst_step : forall t t' x s,
  t ==> t' -> [x := s] t ==> [x := s] t'.
Proof.
intro t; induction t; intros; subst.
- inversion H.
- inversion H; subst.
  + simpl. destruct (beq_idP x0 x1).
    * subst.
    assert ((tapp (tabs x1 T t12) ([x1 := s] t2)) ==>
      [x1 := ([x1 := s] t2)] t12).
    { apply ST_AppAbs. inversion H3; subst.
      - simpl. destruct (beq_idP x1 x0); apply v_abs.
      - simpl. apply v_nat. }
      
    simpl. assert ([x1 := [x1 := s] t2] t12 =
      [x1 := s] ([x1 := t2] t12)) by (apply subst_order).
    rewrite <- H1. assumption.
    
    * assert (tapp (tabs x1 T ([x0 := s] t12)) ([x0 := s] t2) ==>
      [x1 := [x0 := s] t2] ([x0 := s] t12)).
    { apply ST_AppAbs. apply value_subst. assumption. }
    
    simpl.
    
      
Require Import Omega.

(*YES, I THINK THIS IS CORRECT, FIGHT ME!*)
Theorem subst_complex : forall (x : id) s t nt ns,
  complex t nt -> complex s ns ->
  complex ([x := s] t)
    (nt + (appears_count x t)*ns).
Proof.
intros x0 s t. generalize dependent x0;
generalize dependent s; induction t; intros;
rename x0 into x.
- inversion H.
- (*tapp*) simpl. inversion H; subst.

assert (complex ([x := s] t1) (n1 + appears_count x
  t1 * ns)).
{ apply IHt1; auto. }
clear IHt1.

assert (complex ([x := s] t2) (n2 + appears_count x
  t2 * ns)).
{ apply IHt2; auto. }
clear IHt2.

remember (n1 + appears_count x t1 * ns) as n1'.
remember (n2 + appears_count x t2 * ns) as n2'.

assert (complex (tapp ([x := s] t1) ([x := s] t2))
  (n1' + (appears_count x ([x := s] t1)) * n2' + 1)).
{ eapply C_App; try assumption. }



(*This is what I want to prove the most*)
Theorem step_reduce_complex :
  forall t t' n, t ==> t' ->
  complex t n -> complex t' (n - 1).
Proof. intros t; induction t; subst; intros.
- inversion H.
- inversion H0; subst. inversion H; subst.
  + 















Definition self_app := tapp (tvar x) (tvar x).
(*You can't write the loop function below*)
Definition loop := (tabs x ??? (self_app self_app)).
(*Is this well-typed? Probably no, but how can we prove that?*)
Lemma loop_well_typed :
  empty |- loop \in (TArrow Func Func)

(** [] *)

End STLCArith.

(** $Date: 2016-12-20 12:03:19 -0500 (Tue, 20 Dec 2016) $ *)














