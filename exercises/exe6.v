Require Import Setoid.

Inductive le: nat -> nat -> Prop :=
| le_n n: le n n
| le_S n m (H: le n m): le n (S m).

Notation "m <= n" := (le m n).

Definition lt (n m: nat) :=  le (S n) m.
Notation "m < n" := (lt m n).

Lemma le_trans: forall m n o, 
    m <= n -> n <= o -> m <= o.
Proof.
    intros.
    generalize dependent H.
    generalize dependent m.
    induction H0.
    - intros. apply H.
    - intros. 
      apply IHle in H.
      apply le_S.
      apply H.
Qed. 

Lemma O_le_n: forall n, 0 <= n.
Proof.
    intro n.
    induction n.
    - apply le_n.
    - apply le_S in IHn.
    apply IHn.
Qed.

Theorem nleS: forall m n,
    m <= n -> S m <= S n.
Proof.
    intros.
    induction H.
    - apply le_n.
    - apply le_S in IHle. apply IHle.
Qed.

Theorem snls: forall m n,
    S m <= S n -> m <= n.
Proof.
    intros.
    inversion H.
    - apply le_n.
    - apply le_trans with (n := S m). (* what? *)
      + apply le_S. apply le_n.
      + apply H2.
Qed.

Theorem le_plus: forall a b,
    a <= a + b.
Proof.
    intros.
    induction a.
    - simpl. apply O_le_n.
    - simpl. apply nleS. apply IHa.
Qed.

Lemma swap: forall m n, m + n = n + m. Admitted.

Theorem plus_rt: forall n1 n2 m,
    m <= n1 \/ m <= n2 ->
    m <= n1 + n2.
Proof.
    intros.
    destruct H.
    - apply le_trans with (n := n1).
      apply H. apply le_plus.
    - apply le_trans with (n := n2).
      apply H. rewrite swap. apply le_plus.
Qed.

(*
contrapostive of plus_lt
*)

Theorem lt_S: forall n m,
    n <= m -> n <= S m.
Proof.
    intros. 
    inversion H.
    - apply le_S. apply le_n.
    - apply le_S. apply le_S. apply H0.
Qed.
