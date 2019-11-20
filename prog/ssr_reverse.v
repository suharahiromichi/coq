
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Inductive append : seq nat -> seq nat -> seq nat -> Prop :=
| app_nil (b : seq nat) : append [::] b b
| app_cons (n : nat) (a b c : seq nat) : append a b c -> append (n :: a) b (n :: c)
.

Fixpoint app (a b : seq nat) : seq nat :=
  match a with
  | [::] => b
  | n :: a => n :: app a b
  end.

Lemma test : forall (a b c : seq nat), append a b c <-> app  a b = c.
Proof.
  split.
  - elim=> b'' //= a' b' c' H IH.
      by rewrite IH.
  - elim: a b c => //=.
    + move=> b c ->.
        by apply: app_nil.
    + move=> n' a' IH b' c' <-.
      apply: app_cons.
        by apply: IH.
Qed.



Inductive reverse : seq nat -> seq nat -> Prop :=
| rev_nil : reverse [::] [::]
| rev_cons (n : nat) (a b c : seq nat) :
    reverse a b -> append b [:: n] c -> reverse (n :: a) c
.

Fixpoint rev (a : seq nat) : seq nat :=
  match a with
  | [::] => [::]
  | n :: a => app (rev a) [:: n]
  end.

Goal forall (a b : seq nat), reverse a b <-> rev a = b.
Proof.
  split.
  - elim=> //= n a' b' c' H1 H2 H3.
    apply/test.
      by rewrite H2.
  - elim: a b.
    + move=> b' <- /=.
      by apply: rev_nil.
    + move=> n a IH c H.
      simpl in H.
      apply: rev_cons.
      * by apply: IH.
      * by apply/test.
Qed.


Inductive reverse2 : seq nat -> seq nat -> seq nat -> Prop :=
| rev2_nil (b : seq nat) : reverse2 [::] b b
| rev2_cons (n : nat) (a b c : seq nat) :
    reverse2 a (n :: b) c -> reverse2 (n :: a) b c
.

Goal reverse2 [:: 1;2;3] [::] [:: 3;2;1].
Proof.
  apply: rev2_cons.
  apply: rev2_cons.
  apply: rev2_cons.
  apply: rev2_nil.
Qed.

Fixpoint rev2 (a b : seq nat) : seq nat :=
  match a with
  | [::] => b
  | n :: a => rev2 a (n :: b)
  end.

Compute rev2 [:: 1;2;3] [::].               (* [:: 3;2;1] *)

Lemma test2 : forall (a b c : seq nat), reverse2 a b c <-> rev2 a b = c.
Proof.
  split.
  - by elim=> //=.
  - elim: a b c.
    + move=> b c.
      rewrite /rev2 => <-.
        by apply: rev2_nil.
    + move=> n a IH b c H.
      apply: rev2_cons.
      by apply: IH.
Qed.


Require Import Program.

Program Fixpoint rev2' (a b : seq nat) : {c : seq nat | reverse2 a b c} :=
  match a with
  | [::] => b
  | n :: a => rev2' a (n :: b)
  end.
Next Obligation.
Proof.
    by apply: rev2_nil.
Defined.
Next Obligation.
Proof.
    by apply: rev2_cons.
Defined.

Compute proj1_sig (rev2' [:: 1;2;3] [::]).  (* [:: 3;2;1] *)

(* END *)
