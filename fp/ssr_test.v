From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)
Require Import ssrstar.                     (* S-EXP *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
Backup's FP のインタプリタが書けないことの説明

``Apply program object`` の実装において、
Apply が program についての帰納法になる一方、
ApplyInsret (iota) や ApplyAll (alpha) が object についての帰納法になる。

このような相互再帰は、Coq では許されないようである。
*)

Fail Fixpoint test1 (a b : seq nat) {struct a} :=
  match a with
  | [::] => 0
  | a1 :: a2 => test2 a2 b
  end
with test2 (a b : seq nat) {struct b}  :=
  match b with
  | [::] => 0
  | b1 :: b2 => test1 a b2
  end.

Program Fixpoint test1' (a b : seq nat) {size a} :=
  match a with
  | [::] => 0
  | a1 :: a2 => test2' a2 b
  end
with test2' (a b : seq nat) {size b}  :=
  match b with
  | [::] => 0
  | b1 :: b2 => test1' a b2
  end.
Obligations.

(* END *)
