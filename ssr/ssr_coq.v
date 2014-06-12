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

Theorem le_min'' : forall m n, m <= n -> min'' m n = m.
Proof.
  move=> n p H.
  rewrite /min''.
  move/leP in H.
  case: H.                                  (* H は Prop *)
  + have Hnn : n <= n by apply/idP.         (* Hnn は bool *)
    by rewrite Hnn.
  + move=> m Hnm.
    have Hnm1 : n <= m.+1
      by apply leqW; apply/leP; apply Hnm.  (* Hnm1はbool *)
    by rewrite Hnm1.
Qed.

(* END *)
