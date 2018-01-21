(* ProofCafe SF/PLF Support Page *)
(* Smallstep.v *)

(*
これは、ProofCafe の Software Fundations, Vol.2 Programming Language Foundations の
勉強会のサポートページです。復習などに利用しててください。

本ファイルの実行は、本ファイルを pfl ディレクトリの中に混ぜて置くか、
pfl のオリジナルの適当なファイルの適当な場所にcopy&pasteすることで可能です。
 *)

(* ご注意：

1. 実際の勉強会は、本ファイルではなく、オリジナルのファイルを直接編集・実行しておこないます。
2. 本ファイルには、演習問題の答えは含まれません。
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Import Imp. 
Require Import Smallstep.

(* ProofCafe #72 2018/01/20 *)

(* tm 型のコンストラクタ *)
Check C : nat -> tm.
Check P : tm -> tm -> tm.

(* tm 型の例 *)
Check P (P (C 1) (C 2)) (C 3) : tm.      (* tm 型として正しい。 *)
Fail Check P (P (C 1))  : tm.            (* tm 型として正しくない。 *)

(* big-step *)
Check evalF (P (P (C 1) (C 2)) (C 3)) : nat.

Compute evalF (P (P (C 1) (C 2)) (C 3)).    (* = 6 : nat *)


(* small-step *)
Check P (P (C 1) (C 2)) (C 3) ==> P (C 3) (C 3) : Prop.

Compute P (P (C 1) (C 2)) (C 3) ==> P (C 3) (C 3).

Goal P (P (C 1) (C 2)) (C 3) ==> P (C 3) (C 3).
Proof.                                      (* 証明してみる。 *)
  (* goal : P (P (C 1) (C 2)) (C 3) ==> P (C 3) (C 3) *)
  constructor.
  (* goal : P (C 1) (C 2) ==> C 3 *)
  constructor.
  (* No more subgoals. *)
  Show Proof. (* 「証明」を出力する。 *)
  (* (ST_Plus1 (P (C 1) (C 2)) (C 3) (C 3) (ST_PlusConstConst 1 2)) *)
Qed.


(* small-step うまくいかない例 *)
Check P (P (C 1) (C 2)) (C 3) ==> C 6 : Prop.

Goal P (P (C 1) (C 2)) (C 3) ==> C 6.
Proof.                                    (* 証明してみる。 *)
  Fail constructor.                       (* 証明できない。big-step になっているから。 *)
  admit.
Admitted.

(* END *)
