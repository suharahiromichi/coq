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

  Fixpoint fib (n: nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (npp.+1 as np).+1 => fib npp + fib np (* fib n.-2 + fib n.-1 *)
    end.


  Definition P m n :=
    fib (m + n + 1) = fib m * fib n + fib m.+1 * fib n.+1.

  Lemma test0 n : fib 0 * fib n = 0.
  Proof.
      by rewrite mul0n.
  Qed.
  
  Lemma test1 n : fib 1 * fib n = fib n.
  Proof.
      by rewrite mul1n.
  Qed.
        
  Lemma test2 n : fib 2 * fib n = fib n.
  Proof.
      by rewrite mul1n.
  Qed.

  Lemma testn n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.
  
  Goal forall m n, P m n.
  Proof.
    move=> m n.
    rewrite /P.
    elim/nat_ind22 : m.
    - rewrite add0n addn1.
      rewrite test0 test1 add0n.
      done.
      
    - rewrite add1n addn1.
      rewrite test2 test1.      
      rewrite -testn.
      done.
      
    - move=> m IHm IHm1.
      rewrite 2!testn 2!mulnDl.      
      
      rewrite ?addnA [_ + fib m.+1 * fib n.+1]addnC ?addnA.
      rewrite [fib m.+1 * fib n.+1 + fib m * fib n]addnC.
      rewrite -IHm.

      rewrite -?[fib (m + n + 1) + fib m.+1 * fib n + fib m.+2 * fib n.+1]addnA.
      rewrite -IHm1.
      
      have -> : m.+2 + n + 1 = (m + n + 1).+2 by ssromega.
      have -> : m.+1 + n + 1 = (m + n + 1).+1 by ssromega.
      rewrite -testn.
      done.
  Qed.

End Fibonacci.

(* END *)
