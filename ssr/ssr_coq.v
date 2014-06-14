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

Definition min'' m n :=
  match m <= n with
    | true => m
    | false => n
  end.

(**
m < n はすでにboolである。

ssrnat.vに、
Link to the legacy comparison predicates.
として、leP と ltP が定義されている。
*)
Theorem le_min'' : forall m n, m <= n -> min'' m n = m.
Proof.
  move=> n p H.                             (* H は bool *)
  rewrite /min''.
  move/leP in H.                            (* H は Prop *)
  have Hnp : n <= p by apply/leP.           (* Hnp は bool *)
    by rewrite Hnp.
Qed.

(* END *)
