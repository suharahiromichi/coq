(**
Starndard Coq と SSReflect の証明の違い。
-----------------

2014_06_12
@suharahiromichi
*)

(**
# Standard Coq の場合
*)
Require Import Arith Omega.

Check le_lt_dec.
(* : forall m n : nat, {m <= n} + {n < m} *)

Definition min' (m n :nat) :=
  match le_lt_dec m n with
    | left _ => m
    | right _ => n
  end.

Theorem le_min' : forall m n, m <= n -> min' m n = m.
Proof.
  intros m n ; unfold min'.
  case (le_lt_dec m n); simpl.
    trivial.
  intros. omega.
Qed.

(**
# SSReflect の場合
*)
Require Import ssreflect ssrnat ssrbool eqtype.

(* 前提の m <= n からしてboolである。 *)
Theorem le_minn : forall m n, m <= n -> minn m n = m.
Proof.
  move=> n p.
  move/minn_idPl.
  by [].
Qed.

(**
## 説明的な証明
*)
Definition min'' m n :=
  (*  if m < n then m else n. *)
  match m < n with
    | true => m
    | false => n
  end.
Definition max'' m n := if m < n then n else m.

Lemma max'C {m n} : max'' m n = max'' n m.
Proof.
  by rewrite /max''; case ltngtP.
Qed.

Lemma max'E m n : max'' m n = m + (n - m).
Proof.
  rewrite /max'' addnC.
  case: leqP => [/eqnP-> | /ltnW/subnK].
  by [].
  by [].
Qed.

Lemma max'_idPl {m n} : reflect (max'' m n = m) (m >= n).
Proof.
  rewrite -subn_eq0 -(eqn_add2l m) addn0 -max'E.
  by apply: eqP.
Qed.

Lemma max'_idPr {m n} : reflect (max'' m n = n) (m <= n).
Proof.
  by rewrite max'C; apply: max'_idPl.
Qed.

Lemma min'_idPl {m n} : reflect (min'' m n = m) (m <= n).
Proof.
  rewrite (sameP max'_idPr eqP).
  rewrite -(eqn_add2l m) eq_sym -addn_min_max eqn_add2r.
  by apply: eqP.
Qed.

Theorem le_min'' : forall m n, m <= n -> min'' m n = m.
Proof.
  move=> n p.
  move/min'_idPl.
  by [].
Qed.

(* END *)
