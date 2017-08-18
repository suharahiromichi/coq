(** ProofCafe Coq入門 #2 *)
(** 2017/8/19 @suharahiromichi  *)

Set Implicit Arguments.

(* 自然数 *)
Require Import Arith.

Goal forall x y z : nat, x * (y * z) = x * y * z.
Proof.
  intros.
  Search (_ * (_ * _)).
  (* Search では Notation は見つからない。 *)
  now rewrite mult_assoc.                   (* Notation *)
  Undo 1.
  now rewrite Nat.mul_assoc.
  Undo 1.
  ring.
Qed.

Goal forall x : nat, 1 * x = x.
Proof.
  intros.
  now rewrite mult_1_l.                     (* Notation *)
  Undo 1.
  now rewrite Nat.mul_1_l.
  Undo 1.
  ring.
Qed.

Goal forall x : nat, x * 1 = x.
Proof.
  intros.
  now rewrite mult_1_r.                     (* Notation *)
  Undo 1.
  now rewrite Nat.mul_1_r.
  Undo 1.
  ring.
Qed.

(* 整数 *)
Require Import ZArith.
Open Scope Z.

(* Scope については、以下を参照のこと。

   Coq RM
   Chapter 12  Syntax extensions and interpretation scopes
   12.2  Interpretation scopes

   https://coq.inria.fr/refman/Reference-Manual014.html

   主なコマンドは、Bind Scope, Open Scope, Close Scoep.
   省略時解釈は、core_scope, type_scope, nat_scope の順番である。
 *)

Goal forall x y z : Z, x * (y * z) = x * y * z.
Proof.
  intros.
  now rewrite Zmult_assoc.                  (* Notation *)
  Undo 1.
  Search (_ * (_ * _)).                     (* Scope はSearchに影響するよう。 *)
  now rewrite Z.mul_assoc.
  Undo 1.
  ring.
Qed.

Goal forall x : Z, 1 * x = x.
Proof.
  intros.
  now rewrite Zmult_1_l.                    (* Notation *)
  Undo 1.
  now rewrite Z.mul_1_l.
  Undo 1.
  ring.
Qed.

Goal forall x : Z, x * 1 = x.
Proof.
  intros.
  now rewrite Zmult_1_r.                    (* Notation *)
  Undo 1.
  now rewrite Z.mul_1_r.
  Undo 1.
  ring.
Qed.

(* END *)
