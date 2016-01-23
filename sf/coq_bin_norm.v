Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope coq_nat_scope.

Inductive bin :=
| o : bin -> bin
| i : bin -> bin
| z : bin.

Check (i (i (o z))).

Fixpoint binnat (b : bin) : nat :=          (* f *)
  match b with
  | z => 0
  | o b => 2 * (binnat b)
  | i b => 2 * (binnat b) + 1
  end.

Compute binnat (o (i (i (o (o z))))).

Fixpoint bininc (b : bin) : bin :=
  match b with
  | i b => o (bininc b)
  | o b => i b
  | z => i z
  end.

Compute bininc (o (i (i (o (o z))))).
Compute bininc (i (i (i (o (o z))))).
Compute bininc (o (i (i z))).
Compute bininc (i (i (i z))).

Fixpoint natbin (n : nat) : bin :=          (* g *)
  match n with
  | 0 => z
  | n.+1 => bininc (natbin n)
  end.

(* 直接的な正規化 *)
Fixpoint normalize (b : bin) : bin :=
  match b with
  | o b =>
    match (binnat b) with
    | 0 => z
    | _ => o (normalize b)
    end
  | i b => i (normalize b)
  | z => z
  end.

Compute normalize (o (i (i (o (o z))))).
Compute natbin (binnat (o (i (i (o (o z)))))).

Lemma test' n : n + n.+2 = 2 * n.+1.
Proof.
  Search (2 * _).
  simpl.
  rewrite NPeano.Nat.add_0_r.
  by [].
Qed.

Lemma hodai1 n :
  natbin (2 * n.+2) = o (natbin n.+2).
Proof.
  elim: n.+1.
  - by [].
  - move=> n' H /=.
    Search (_ + 0).
    rewrite NPeano.Nat.add_0_r.
    rewrite test'.
    by rewrite H /=.
Qed.

Lemma hodai2 n :
  natbin (2 * n.+2 + 1) = i (natbin n.+2).
Proof.
  elim: n.+1.
  - by [].
  - move=> n' H /=.
    rewrite NPeano.Nat.add_0_r.
    rewrite test'.
    by rewrite H /=.
Qed.

(* natを経由する正規化と、直接的な正規化が、同じ結果になることを証明する。 *)
Goal forall (b : bin),
    natbin (binnat b) = normalize b.
Proof.
  induction b.
  - simpl.
    rewrite <- IHb.
    case (binnat b).
    + simpl.
      reflexivity.
    + intros n.
      induction n.
      * simpl.
        reflexivity.
      * by apply hodai1.
  - simpl.      
    rewrite <- IHb.
    case (binnat b).
    + simpl.
      reflexivity.
    + intros n.
      induction n.
      * simpl.
        reflexivity.
      * by apply hodai2.
  - simpl.
    reflexivity.
Qed.
