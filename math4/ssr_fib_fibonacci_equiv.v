From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssrZ zify ring lra.

(**
普通の定義
*)
Fixpoint fibonacci n :=
  match n with
  | 0 => 0
  | 1 => 1
  | (m.+1 as pn).+1 => fibonacci m + fibonacci pn
  end.

Lemma fibonacci_add n : fibonacci n + fibonacci n.+1 = fibonacci n.+2.
Proof.
  done.
Qed.

(**
高速計算版
*)
Fixpoint loop n :=
  match n with
  | 0 => (0, 1)
  | m.+1 => let: p := loop m in (p.2, p.1 + p.2)
  end.
Definition fib n := (loop n).1.

Goal [seq fib x | x <- [:: 0; 1; 2; 3; 4; 5]] = [:: 0; 1; 1; 2; 3; 5].
Proof.
  done.
Qed.

Lemma fib_add n : fib n + fib n.+1 = fib n.+2.
Proof.
  by rewrite /fib /loop.
Qed.

(**
普通の定義と高速計算版が同じ結果を返すことを証明する。
*)
Lemma fibonacci_equiv : fibonacci =1 fib.
Proof.
  move=> m.
  case: (ubnPgeq m);
    elim: m => [n | n IHn [// | [// |]] m H].
  - by rewrite leqn0 => /eqP ->.
  - rewrite -fib_add -fibonacci_add.
    congr (_ + _); apply: IHn; lia.
Qed.

(**
MathComp風、完全帰納法の結果：

  n : nat
  IHn : forall n0 : nat, n0 <= n -> fibonacci n0 = fib n0
  m : nat
  H : m.+1 < n.+1
  ============================
  fibonacci m.+2 = fib m.+2
*)

(* END *)
