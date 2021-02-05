Inductive even: nat -> Prop :=
| even_0 : even 0
| even_SS (n : nat) (H: even n) : even (S (S n)).

Theorem ev_inversion: 
    forall (n: nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
    intros n H.
    destruct H as [| n' E].
    - left. reflexivity.
    - right.
      exists n'.
      split. reflexivity. apply E.
Qed.

Theorem evSS_ev: forall n,
    even (S (S n)) -> even n.
Proof.
    intros.
    apply ev_inversion in H.
    destruct H.
    - discriminate H.
    - destruct H as [n'  [Hnm Hev]].
      injection Hnm.
      intro. rewrite H. apply Hev.  
Qed.

Theorem evSS_ev2: forall n,
    even (S (S n)) -> even n.
Proof.
    intros n E.
    inversion E.
    apply H0.
Qed.

Theorem even5n: 
    even 5 -> 2 + 2 = 9.
Proof.
    intro H.
    inversion H.
    inversion H1.
    inversion H3.
Qed.

Fixpoint double (n: nat) :=
    match n with
    | 0 => 0
    | S n' => S (S (double n'))
    end.

Lemma ev_even: forall n,
    even n -> exists k, n = double k.
Proof.
    intros n H.
    inversion H.
    - exists 0. simpl. reflexivity.
Abort.

Theorem ev_even1: forall n,
    even n -> exists k, n = double k.
Proof.
    intros n E.
    induction E as [| n' E' IH].
    - exists 0. reflexivity.
    - destruct IH as [k IHk].
      rewrite IHk.
      exists (S k).
      reflexivity.
Qed.

Lemma add0: forall n, n + 0 = n. Admitted.
Lemma adds: forall n m, n + S m = S (n + m). Admitted.

Theorem ev_sum: 
    forall n m, even n -> even m -> even (n + m).
Proof.
    intros n m H1 H2.
    induction H1 as [| x].
    + simpl. apply H2.
    + inversion H2. 
      simpl. rewrite add0. apply even_SS. apply H1.
      rewrite H0.
      simpl. apply even_SS. apply IHeven.
Qed.

Lemma ev_ev_s: forall n m,
    even (n + m) -> even n -> even m.
Proof.
    intros n m H1 H2.
    induction H2 as [| x E IHx].
    - simpl in H1. apply H1.
    - simpl in H1. apply evSS_ev2 in H1.
      apply IHx in H1.
      apply H1.
Qed.

Inductive le: nat -> nat -> Prop :=
| le_n n: le n n
| le_S n m (H: le n m): le n (S m).

Notation "m <= n" := (le m n).

Definition lt (n m: nat) :=  le (S n) m.
Notation "m < n" := (lt m n).

