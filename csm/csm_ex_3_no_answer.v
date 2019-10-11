(**
Coq/SSReflect/MathComp による定理証明

第3章 演習問題と追加の問題、回答付き

======

2018_10_11 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 問 3.1  *)
(** 赤玉と白玉のふたつの要素からなる型「紅白玉」をInductiveを使って定
    義してください。 *)
(** Exercise 3.1 *)
(** Define the type "ball" that consists of two elements, red (rouge)
    and white (blanc). *)

(** 問 3.2 *)
(** ボールの列の型をlist型を使って定義してください。 *)
(** Exercise 3.2 *)
(** Dinefine the type of sequence of balls using the "list" (or "seq") type. *)

(** 問 3.3 *)
(** 次のうち、正しい型をもつ値はどれでしょうか。Checkコマンドを使って
    確認してください。 *)
(** Exercise 3.3 *)
(** Which of the following values ​​has the correct type? Confirm using
    the "Check" command. *)

(** 問 3.4 *)
(** Fixpint コマンドを使って、型 balls -> nat を持つ関数 count_rouges
    を定義してください。以下に動作例を示します。 *)
(** そして、Compute コマンドを使って確認してください。 *)
(** Exercise 3.4 *)
(** Define the function "count_rouges" which has the "balls -> nat"
    type, using "Fixpoint" command. *)
(** Examples of function values are shown below. *)
(**
   count_rouges nil                           ==> 0
   count_rouges (cons rouge nil)              ==> 1
   count_rouges (cons blanc nil)              ==> 0
   count_rouges (cons rouge (cons rouge nil)) ==> 2
   *)
(* And confirm using the "Compute" command. *)

(* END *)
