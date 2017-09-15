Add LoadPath "/home/khoa/Coq/sf".
Require Export Poly.
Require Export IndProp.

(*Somehow I have to rewrite 'In'*)
Fixpoint In {T : Type} (t : T) (l : list T) : Prop := match l with
  | nil => False
  | hd :: tl => (t = hd) \/ In t  tl
end.

(*The node type*) (*if it has one constructor, it is a Prop,
if it has two, it is a set*)
Inductive node : Type := | Node: node.
(*The network type*)
Definition network := list node.
(*The 'connected' property*)
Inductive Pconnect : node -> node -> Prop := 
  | Connect_refl : forall n, Pconnect n n
  | Connect_comm : forall n m, Pconnect n m -> Pconnect m n
  | Connect_trans : forall n m o, Pconnect n m -> 
    Pconnect m o -> Pconnect n o.

(*When you get the Internet going*)
Definition interconnected (l : network) : Prop := 
  forall (m n : node), In m l /\ In n l -> Pconnect m n.

(*The star network topoloty*)
Definition star (l : network) : Prop :=
  exists (x : node), forall (y : node), In y l -> Pconnect x y.

(*star == Internet*)
Theorem star_interconnected : forall (l : _),
  star l -> interconnected l.
Proof.
  unfold star. unfold interconnected. intros. destruct H. destruct H0.
  apply Connect_trans with x.
  + apply Connect_comm. apply H. auto.
  + apply H. auto.
Qed.

(*Ring network (Not really, but I guess it doesn't matter*)
Inductive ring_topo : network -> Prop :=
  | ring_base : forall n1 n2, Pconnect n1 n2 -> ring_topo [n1; n2]
  | ring_next : forall n1 n2 (l : network), ring_topo (n2 :: l) -> 
    (Pconnect n1 n2) -> ring_topo (n1 :: n2 :: l).

(*ring_topo == Internet*)
Theorem ring_interconnected : forall (l : _),
  ring_topo l -> interconnected l.
Proof. intros. unfold interconnected. induction H.
- intros. destruct H0. simpl in H0. simpl in H1.
destruct H0; destruct H1; destruct H0; destruct H1; subst;
try apply Connect_refl; try contradiction; auto.
apply Connect_comm. auto.
- intros. destruct H1. 
replace (In m (n1 :: n2 :: l)) with (m = n1 \/ In m (n2 :: l)) in H1.
Focus 2. auto.
replace (In n (n1 :: n2 :: l)) with (n = n1 \/ In n (n2 :: l)) in H2.
Focus 2. auto.
destruct H1; destruct H2; subst.
  + apply Connect_refl.
  + simpl in H2. destruct H2; subst. * auto.
    * apply Connect_trans with n2. auto.
    apply IHring_topo. split. simpl; left; auto. simpl; right; auto.
  + apply Connect_trans with n2.
    * simpl in H1. destruct H1; subst. apply Connect_refl.
    apply IHring_topo. split. simpl; right; auto.
    simpl; left; auto.
    * apply Connect_comm; auto.
  + apply IHring_topo; auto.
Qed. 






  

