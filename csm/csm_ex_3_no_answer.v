(**
Coq/SSReflect/MathComp による定理証明

第3章 演習問題と追加の問題、回答なし。

======

2018_09_16 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 問 3.1 *)

Inductive 紅白玉 :=
| 赤玉
| 白玉
.

(** 問 3.2 *)

Definition 玉の列 := list 紅白玉.

(** 問 3.3 *)

Check nil : 玉の列.
Fail Check 赤玉      : 玉の列.
Check cons 赤玉 nil  : 玉の列.
Fail Check nil cons 赤玉 nil : 玉の列.
Check cons 白玉 (cons 赤玉 nil).

(** 問 3.4 *)
(* 0 を適当な定義に置き換えてください。 *)

Fixpoint 赤数え (s : 玉の列) : nat :=
  0.
  
(** 問 3.5 追加の問題 *)
(** 与えられた玉の列に対する赤玉の数を示す述語 num_of_red を Inductive により定義せよ。 *)
(* 2箇所ある True を適当な論理式に書き換えてください。それぞれ別の式です。 *)

Inductive num_of_red : 玉の列 -> nat -> Prop :=
| b_nil : num_of_red nil 0
| b_red : forall s n, True -> num_of_red (赤玉 :: s) n
| b_white : forall s n, True -> num_of_red (白玉 :: s) n
.

(** 問 3.6 追加の問題 *)
(** 命題 [num_of_red (cons 白玉 (cons 赤玉 nil)) 1] が真であることを示せ。 *)
(* Admitted を修正してください。 *)

Goal num_of_red (cons 白玉 (cons 赤玉 nil)) 1.
Proof.
Admitted.

(** 問 3.7 追加の問題 *)
(** 命題 [num_of_red (cons 白玉 (cons 赤玉 nil)) 0] が偽（否定が真）であることを示せ。 *)
(* Admitted を修正してください。 *)

Goal ~ num_of_red (cons 白玉 (cons 赤玉 nil)) 0.
Proof.
Admitted.

(** 問 3.8 追加の問題 *)
(** 問 3.4 で定義した 関数 赤数え の結果と、問 3.5 で定義した 述語
    num_of_red の命題が必要十分条件であることを定理として示せ。
    このとき、num_of_red の定義を見直してもよい。 *)
(* admit と Admitted を修正してください。 *)

Theorem 赤数え_赤の数 s n : 赤数え s = n <-> num_of_red s n.
Proof.
  split.
  - admit.
  - admit.
Admitted.

(* END *)
