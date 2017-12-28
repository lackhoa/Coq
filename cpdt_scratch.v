Add LoadPath "/home/khoa/Coq/cpdtlib".
Require Export CpdtTactics.

Inductive even_list : Set :=
  | ENil : even_list
  | ECons : nat -> odd_list -> even_list

with odd_list : Set :=
  | OCons : nat -> even_list -> odd_list.
(*What? This is so meta!*)

Fixpoint elength (el : even_list) : nat :=
  match el with
    | ENil => O
    | ECons _ ol => S (olength ol)
  end

with olength (ol : odd_list) : nat :=
  match ol with
    | OCons _ el => S (elength el)
  end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
    | ENil => el2
    | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
    | OCons n el' => OCons n (eapp el' el)
  end.

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
  induction el1; crush.
  Abort.
  
Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop.

Check even_list_mut.

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
Proof.
apply (even_list_mut
  (fun el1: even_list => forall el2: even_list, elength (eapp el1 el2) = elength el1 + elength el2)
  (fun ol1: odd_list => forall el2: even_list, olength (oapp ol1 el2) = olength ol1 + elength el2)); intros.
- crush.
- simpl. rewrite H. auto.
- simpl. rewrite H. auto.
Qed. (*Awesome!*)

(*==================Reflexive type==============*)
Inductive pformula : Set :=
  | Truth : pformula
  | Falsehood : pformula
  | Conjunction : pformula -> pformula -> pformula.

Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
    | Truth => True
    | Falsehood => False
    | Conjunction f1 f2 => pformulaDenote f1 /\ pformulaDenote f2
end.

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula.

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
    | Eq n1 n2 => n1 = n2
    | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
    | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

Fixpoint swapper (f : formula) : formula :=
  match f with
    | Eq n1 n2 => Eq n2 n1
    | And f1 f2 => And (swapper f2) (swapper f1)
    | Forall f' => Forall (fun n => swapper (f' n))
  end.

Theorem swapper_preserves_truth : forall f, formulaDenote f -> formulaDenote (swapper f).
Proof.
induction f; intros.
- simpl. inversion H. auto.
- simpl. inversion H. apply IHf1 in H0;
apply IHf2 in H1. auto.

- (*The big case*)
simpl. simpl in H0. intro.
eapply H in H0. apply H0.
Qed.
















