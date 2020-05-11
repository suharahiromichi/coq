(* fib k*n は fib k の倍数である。  *)
(* http://parametron.blogspot.com/2017/03/blog-post.html *)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ffibonacci *)

Section Fibonacci.
(*
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
*)
  
  Variable nat_ind22
    : forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P n.+1 -> P n.+2) ->
      forall n : nat, P n.

(**
fibonacci 関数
*)

  Fixpoint fib (n: nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (npp.+1 as np).+1 => fib npp + fib np (* fib n.-2 + fib n.-1 *)
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
      
      rewrite ?addnA [_ + fib m.+1 * fib n.+1]addnC ?addnA.
      rewrite [fib m.+1 * fib n.+1 + fib m * fib n]addnC.
      rewrite -IHm.

      rewrite -?[fib (m + n + 1) + fib m.+1 * fib n + fib m.+2 * fib n.+1]addnA.
      rewrite -IHm1.
      
      have -> : m.+2 + n + 1 = (m + n + 1).+2 by ssromega.
      have -> : m.+1 + n + 1 = (m + n + 1).+1 by ssromega.
      rewrite -fib_n.
      done.
  Qed.

  Lemma n2__n1_1 n : n.+2 = n.+1 + 1.
  Proof.
      by ssromega.
  Qed.
  
(**
fib k*n は fib k の倍数である。
nについての帰納法で解く。
 *)

  Lemma fibkn_divs_fibk k n : fib k.+1 %| fib (k.+1 * n.+1).
  Proof.
    elim: n.
    - rewrite muln1.
      done.
    - move=> n IHn.
      have -> : k.+1 * n.+2 = k.+1 * n.+1 + k + 1
        by rewrite n2__n1_1 mulnDr muln1-{2}[k.+1]addn1 ?addnA.
      rewrite fib_m_n_1.
      apply: dvdn_add.
      + by apply: dvdn_mulr.
      (* fib k.+1 %| fib (k.+1 * n.+1) -> fib k.+1 %| fib (k.+1 * n.+1) * _ *)
      + by apply: dvdn_mull.
        (* fib k.+1 %| _ * fib k.+1 *)
  Qed.
  
(*
  Lemma fib_m_n m n :
    fib (m + n) = fib m.-1 * fib n + fib m * fib n.+1.
  Proof.
  Admitted.
  
  Lemma fibkn_divs_fibn' k n : fib k %| fib (k * n).
  Proof.
    elim: n.
    - rewrite muln0.
      done.
    - move=> n IHn.
      have -> : k * n.+1 = k * n + k. by rewrite -addn1 mulnDr muln1.
      rewrite fib_m_n.
      apply: dvdn_add.
      + by apply: dvdn_mull.                (* fib k %| _ * fib k *)
      + by apply: dvdn_mulr.
        (* fib k %| fib (k * n) -> fib k %| fib (k * n) * _ *)
  Qed.
*)

End Fibonacci.

(* END *)
