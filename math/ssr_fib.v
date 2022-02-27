(**
フィボナッチ数列についての定理の証明

F(k * n) は F(k) の倍数である、など。

参考：  http://parametron.blogspot.com/2017/03/blog-post.html
*)

From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.
Require Import Recdef.                      (* Function *)

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
*)

(**
# fibonacci 関数の定義
*)
  (* Require Import Recdef. *)
  Function fib (n: nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.
  (* functional induction (fib m) で使われる。 *)
  Check fib_ind
     : forall P : nat -> nat -> Prop,
       (forall n : nat, n = 0 -> P 0 0) ->
       (forall n : nat, n = 1 -> P 1 1) ->
       (forall n m : nat,
        n = m.+2 -> P m (fib m) -> P m.+1 (fib m.+1) -> P m.+2 (fib m + fib m.+1)) ->
       forall n : nat, P n (fib n).
  
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
補題：フィボナッチ数列の加法定理

参考文献では、

```F(m + n) = F(m) * F(n+1) + F(m-1) * F(n)```

一旦、mをm+1に変更し（右辺を昇順にして）証明した。
さらに、m ≧ 1 の条件を追加して証明した。
*)  
  Lemma fib_addition' m n :
    fib (m + n + 1) = fib m * fib n + fib m.+1 * fib n.+1.
  Proof.
    functional induction (fib m).           (* fib_ind *)
    - rewrite add0n addn1.
      rewrite fib_0 fib_1 add0n.
      done.
      
    - rewrite add1n addn1.
      rewrite fib_2 fib_1.      
      rewrite -fib_n.
      done.
      
    - rewrite 2!fib_n 2!mulnDl.      
      
      (* F(m + n + 1) の項をまとめて置き換える *)
      rewrite ?addnA [_ + fib m.+1 * fib n.+1]addnC ?addnA.
      rewrite [fib m.+1 * fib n.+1 + fib m * fib n]addnC.
      rewrite -IHn0.
      
      (* F(m.+1 + n + 1) の項をまとめて置き換える *)
      rewrite -?[fib (m + n + 1) + fib m.+1 * fib n + fib m.+2 * fib n.+1]addnA.
      rewrite -IHn1.
      
      have -> : m.+2 + n + 1 = (m + n + 1).+2 by ssromega.
      have -> : m.+1 + n + 1 = (m + n + 1).+1 by ssromega.
      rewrite -fib_n.
      done.
  Qed.
  
  Lemma fib_addition m n :
    1 <= m -> fib (m + n) = fib m * fib n.+1 + fib m.-1 * fib n.
  Proof.
    move=> H.
    have H' := fib_addition' m.-1 n.
    rewrite -?addnA addnCA addn1 prednK in H'.
    - rewrite addnC.
      rewrite [fib m * fib n.+1 + fib m.-1 * fib n]addnC.
      done.
    - done.
  Qed.
  
(**
F(n * k) は F(k) の倍数である。

n についての帰納法で解く。

一旦、Coqの帰納法にあわせて、n と k ともに n+1 と k+1 として証明したのち、
k ≧ 1 と n ≧ 1 の条件をつけて証明する。
*)
  Lemma dvdn_1 k m n : k %| m -> k %| m * n.
  Proof.
      by apply: dvdn_mulr.
  Qed.
  
  Lemma dvdn_2 k m : k %| m * k.
  Proof.
      by apply: dvdn_mull.
  Qed.
  
  Lemma fibkn_divs_fibk' k n : fib k.+1 %| fib (n.+1 * k.+1).
  Proof.
    elim: n.
    - rewrite mul1n.
      done.
    - move=> n IHn.
      have -> : n.+2 * k.+1 = n.+1 * k.+1 + k + 1
        by rewrite -addn1  mulnDl mul1n -?addnA addn1.
      rewrite fib_addition'.
      apply: dvdn_add.
      + by apply: dvdn_1.                   (* IHn 使う *)
      + by apply: dvdn_2.
    Qed.
  
  Lemma fibkn_divs_fibk k n : 1 <= k -> 1 <= n -> fib k %| fib (n * k).
  Proof.
    move=> Hk Hm.
    have H' := fibkn_divs_fibk' k.-1 n.-1.
    rewrite prednK in H'; last done.
    rewrite prednK in H'; last done.
    done.
  Qed.
  

(**
参考文献では、

```F(n.+1) * F(n.-1) - F(n)^2 = (-1)^n```

すなわち、nが偶数なら1、奇数なら-1。
参考文献ならば、n についての単純な帰納法で証明できる。ただしP(1)を底にする。

ここでは、Coqの帰納法にあわせて n, n.+1, n.+2 とする（偶数なら-1、奇数なら1）とともに、
(-1)が使えないので、偶数と奇数で、引き算の方向を逆にして、つねに1と比較する。

nat_ind2 を使って証明する。
*)  

  Lemma oddn2 n : odd n.+2 = odd n.
  Proof.
    rewrite /=.
    by rewrite negbK.
  Qed.

  Lemma oddn1 n : odd n.+1 = ~~ odd n.
  Proof.
    done.
  Qed.
  
  Lemma odd_pred n : 1 <= n -> odd n.-1 = ~~ odd n.
  Proof.
    elim: n => [// | n IHn H].
      by rewrite succnK oddn1 negbK.
  Qed.
  
  Lemma fibfib_fib2 n : fib n.+3 * fib n.+1 - fib n.+2 * fib n.+2 =
                        fib n.+1 * fib n.+1 - fib n.+2 * fib n.
  Proof.
    rewrite [fib n.+3]fib_n.
    rewrite {2}[fib n.+2]fib_n.
    rewrite 2!mulnDl.
    rewrite [fib n.+2 * fib n.+1]mulnC.
    rewrite subnDr.
    rewrite [fib n.+2 * fib n]mulnC.
    done.
  Qed.
  
  Lemma fib2_fibfib n : fib n.+2 * fib n.+2 - fib n.+3 * fib n.+1 =
                        fib n.+2 * fib n - fib n.+1 * fib n.+1.
  Proof.
    rewrite [fib n.+3]fib_n.
    rewrite {1}[fib n.+2]fib_n.
    rewrite 2!mulnDl.
    rewrite [fib n.+2 * fib n.+1]mulnC.
    rewrite subnDr.
    rewrite [fib n.+2 * fib n]mulnC.
    done.
  Qed.
  
  Lemma fib_o n :
    fib n.+4 * fib n.+2 - fib n.+3 * fib n.+3 =
    fib n.+2 * fib n - fib n.+1 * fib n.+1.
  Proof.
    rewrite fibfib_fib2.
    rewrite fib2_fibfib.
    done.
  Qed.

  Lemma fib_e n :
    fib n.+3 * fib n.+3 - fib n.+4 * fib n.+2 =
    fib n.+1 * fib n.+1 - fib n.+2 * fib n.
  Proof.
    rewrite fib2_fibfib.
    rewrite fibfib_fib2.
    done.
  Qed.
  
  Lemma fib_e_o' n :
    if odd n then
      fib n.+2 * fib n - (fib n.+1)^2 = 1
    else
      (fib n.+1)^2 - fib n.+2 * fib n = 1.
  Proof.
    rewrite -mulnn.
    elim/nat_ind2 : n => [/= | /= | n IHn].
    - by ssromega.
    - by ssromega.
    - by rewrite oddn2 fib_o fib_e.
  Qed.

  Lemma fib_e_o n :
    1 <= n ->
    if odd n then
      (fib n)^2 - fib n.+1 * fib n.-1 = 1
    else
      fib n.+1 * fib n.-1 - (fib n)^2 = 1.
  Proof.
    move=> Hn.
    have H' := fib_e_o' n.-1.
    rewrite prednK in H'; last done.
    rewrite odd_pred in H' ; last done.
      by rewrite if_neg in H'.
  Qed.
  
End Fibonacci.

(* END *)
