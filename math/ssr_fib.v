(**
フィボナッチ数列についての定理の証明

F(k * n) は F(k) の倍数である、など。

参考：  http://parametron.blogspot.com/2017/03/blog-post.html
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
ffibonacci
 *)

Section Fibonacci.

(**
# 参考

SFの古い版にあった even の証明に使う帰納法の例。
*)
  Definition nat_ind2 :
    forall (P : nat -> Prop),
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P n.+2) ->
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS =>
          fix f (n : nat) := match n return P n with
                             0 => P0
                           | 1 => P1
                           | n'.+2 => PSS n' (f n')
                           end.
  
  Check nat_ind2
    : forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P n.+2) ->
      forall n : nat, P n.

(**
# fib の証明に使う帰納法

公理として与える。修正すること。
*)
  Axiom nat_ind22 : forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P n.+1 -> P n.+2) ->
      forall n : nat, P n.

(**
# fibonacci 関数の定義
*)
  Fixpoint fib (n: nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (ppn.+1 as pn).+1 => fib ppn + fib pn (* fib n.-2 + fib n.-1 *)
    end.

  Lemma fib_0 n : fib 0 * fib n = 0.
  Proof.
      by rewrite mul0n.
  Qed.
  
  Lemma fib_1 n : fib 1 * fib n = fib n.
  Proof.
      by rewrite mul1n.
  Qed.
        
  Lemma fib_2 n : fib 2 * fib n = fib n.
  Proof.
      by rewrite mul1n.
  Qed.

  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.

(**
補題：  nat_ind22 を使って解く。

参考文献では、

```F(m + n) = F(m) * F(n+1) + F(m-1) * F(n)```

Coqの帰納法にあわせて、mをm+1に変更し、右辺を昇順にした。
*)  
  Lemma fib_m_n_1 m n :
    fib (m + n + 1) = fib m * fib n + fib m.+1 * fib n.+1.
  Proof.
    elim/nat_ind22 : m.
    - rewrite add0n addn1.
      rewrite fib_0 fib_1 add0n.
      done.
      
    - rewrite add1n addn1.
      rewrite fib_2 fib_1.      
      rewrite -fib_n.
      done.
      
    - move=> m IHm IHm1.
      rewrite 2!fib_n 2!mulnDl.      
      
      (* F(m + n + 1) の項をまとめて置き換える *)
      rewrite ?addnA [_ + fib m.+1 * fib n.+1]addnC ?addnA.
      rewrite [fib m.+1 * fib n.+1 + fib m * fib n]addnC.
      rewrite -IHm.
      
      (* F(m.+1 + n + 1) の項をまとめて置き換える *)
      rewrite -?[fib (m + n + 1) + fib m.+1 * fib n + fib m.+2 * fib n.+1]addnA.
      rewrite -IHm1.
      
      have -> : m.+2 + n + 1 = (m + n + 1).+2 by ssromega.
      have -> : m.+1 + n + 1 = (m + n + 1).+1 by ssromega.
      rewrite -fib_n.
      done.
  Qed.
  
(**
F(n * k) は F(k) の倍数である。

n についての帰納法で解く。

Coqの帰納法にあわせて、n と k ともに n+1 と k+1 にする。
*)
  Lemma dvdn_1 k m n : k %| m -> k %| m * n.
  Proof.
      by apply: dvdn_mulr.
  Qed.
  
  Lemma dvdn_2 k m : k %| m * k.
  Proof.
      by apply: dvdn_mull.
  Qed.
  
  Lemma fibkn_divs_fibk k n : fib k.+1 %| fib (n.+1 * k.+1).
  Proof.
    elim: n.
    - rewrite mul1n.
      done.
    - move=> n IHn.
      have -> : n.+2 * k.+1 = n.+1 * k.+1 + k + 1
        by rewrite -addn1  mulnDl mul1n -?addnA addn1.
      rewrite fib_m_n_1.
      apply: dvdn_add.
      + by apply: dvdn_1.                   (* IHn 使う *)
      + by apply: dvdn_2.
    Qed.
  
End Fibonacci.

(* END *)
