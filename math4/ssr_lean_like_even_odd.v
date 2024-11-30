(**
Lean 風の Even、Oddの定義と補題の証明
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)

Definition evenP (n : int) := exists (k : int), n = k * 2.
Definition oddP (n : int) := exists k, n = (k * 2) + 1.

Lemma even_add m n : evenP m -> evenP n -> evenP (m + n).
Proof.
(**
in Lean
- have (k1 hk1)
- have (k2 hk2)
- calc m + n = 2 * k1 + n := by rw [hk2]
--  _ = 2 * k1 + 2 * k2   := by rw [hk2]
--  _ = 2 * (k1 + k2)     := by ring
*)
  case=> [k1 hk1].
  case=> [k2 hk2].
  exists (k1 + k2).
  by rewrite hk1 hk2 mulrDl.
Qed.

Lemma odd_even_add m n : oddP m -> evenP n -> oddP (m + n).
Proof.
  case=> [k1 hk1].
  case=> [k2 hk2].
  exists (k1 + k2).
  by rewrite hk1 hk2 mulrDl addrAC.
Qed.

(* END *)
