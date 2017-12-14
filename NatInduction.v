Require Import Omega.

Theorem nat_induc: forall P,
  P 0 ->
  (forall m n, P m -> m < n -> P n) ->
  (forall n, P n).
Proof.
induction n.
- assumption.
- eapply X0. apply IHn. apply le_n.
Qed.