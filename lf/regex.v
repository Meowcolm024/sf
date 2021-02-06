Require Import List.
Import ListNotations.

Inductive reg_exp {T: Type} : Type :=
    | EmptySet
    | EmptyStr
    | Char (t: T)
    | App (r1 r2: reg_exp)
    | Union (r1 r2: reg_exp)
    | Star (r: reg_exp).

Inductive exp_match {T}: list T -> reg_exp -> Prop :=
    | MEmpty: exp_match [] EmptySet
    | MChar x: exp_match [x] (Char x)
    | MApp s1 re1 s2 re2
        (H1: exp_match s1 re1) (H2: exp_match s2 re2):
        exp_match (s1 ++ s2) (App re1 re2)
    | MUnionL s1 re1 re2 (H1: exp_match s1 re1):
        exp_match s1 (Union re1 re2)
    | MUnionR re1 s2 re2 (H1: exp_match s2 re2):
        exp_match s2 (Union re1 re2)
    | MStar0 re: exp_match [] (Star re)
    | MStarApp s1 s2 re
        (H1: exp_match s1 re) (H2: exp_match s2 (Star re)):
        exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example regex2: [1; 2] =~ App (Char 1) (Char 2).
Proof.
    apply (MApp [1] _ [2]).
    - apply MChar.
    - apply MChar.
Qed.

Fixpoint reg_exp_of_list {T} (l: list T) :=
    match l with
    | [] => EmptyStr
    | x::xs => App (Char x) (reg_exp_of_list xs)
    end.

Lemma empty_is_empty: forall T (s: list T),
    ~ (s =~ EmptySet).
Proof.
    intros T s H.
    inversion H.
Abort.
(* Qed. *)

Lemma MUnion': forall T (s: list T) (re1 re2: @reg_exp T),
    s =~ re1 \/ s =~ re2 ->
    s =~ Union re1 re2.
Proof.
    intros.
    destruct H as [P | Q].
    - apply (MUnionL s re1 re2) in P.
      apply P.
    - apply (MUnionR re1 s re2) in Q.
      apply Q.
Qed.

Fixpoint re_chars {T} (re: reg_exp) : list T :=
    match re with
    | EmptySet => []
    | EmptyStr => []
    | Char x => [x]
    | App re1 re2 => re_chars re1 ++ re_chars re2
    | Union re1 re2 => re_chars re1 ++ re_chars re2
    | Star re => re_chars re
    end.