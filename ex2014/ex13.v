Require Import ssreflect.

(**
# 第3回

http://qnighy.github.io/coqex2014/ex3.html

## 課題13 (種別:B / 締め切り : 2014/05/04)

1. 自然数の定義を参考にして、正の整数をあらわすデータ型を帰納的に定義せよ。
2. 自然数の足し算の定義を参考にして、上で定義した正の整数に関する足し算を定義せよ。
3. 上で定義した足し算が結合的であることを証明せよ。
 *)

Inductive pos : Set :=
| SO
| S of pos.

Fixpoint plus (n m : pos) : pos :=
  match n with
    | SO => S m
    | S n' => S (plus n' m)
  end.

Infix "+" := plus.

Theorem plus_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  elim.                                     (* 一番左の数についての帰納法 *)
    by [].
  move=> p H m p0 /=.
  by rewrite (H m p0).
Qed.

(* END *)
