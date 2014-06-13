(**
{0, 1}* のうち0の出現数が1の出現数の丁度2倍であるような列だけを集めた集合は、
S = SS | 00S1 | 1S00 | 0S1S0 | ε というCFGで書き表せることを証明せよ。

https://twitter.com/pi8027/status/476708668239384576

このCFDで生成される文字列の 0の数は 1の数の2倍であることを示す。
（これで、問題の趣旨に合っている？）
*)

Require Import ssreflect ssrnat ssrbool eqtype seq.

Inductive OI : Set :=
| ss of OI & OI
| oosi of OI
| isoo of OI
| osiso of OI
| ε.

Fixpoint icount (l : OI) : nat :=
  match l with
    | ss m n => (icount m) + (icount n)
    | oosi m => (icount m).+1
    | isoo m => (icount m).+1
    | osiso m => (icount m).+1
    | ε => 0
  end.

Fixpoint ocount (l : OI) : nat :=
  match l with
    | ss m n => (ocount m) + (ocount n)
    | oosi m => (ocount m).+2
    | isoo m => (ocount m).+2
    | osiso m => (ocount m).+2
    | ε => 0
  end.

Goal forall l : OI, (icount l).*2 = ocount l.
Proof.
  elim;
  first                                     (* SS *)
    (move=> l H l' H'; by rewrite /= doubleD H H');
  last                                      (* ε *)
    by [];
  (move=> l H /=; by rewrite doubleS H).
Qed.

(* END *)
