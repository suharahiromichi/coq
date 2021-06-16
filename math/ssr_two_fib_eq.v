(**
TwoFibsEq 

https://zenn.dev/blackenedgold/books/introduction-to-idris

Chapter 23 依存型を使った定理証明入門
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import FunInd.                      (* Functional Scheme *)
Require Import Recdef.                      (* Function *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
ffibonacci
 *)
Section Two_Fib_Eq.

(**
# keen さんの定義
*)
  Function fib'1 (n : nat) : nat :=
    match n with
    | 0 => 1
    | 1 => 1
    | (m.+1 as pn).+1 => fib'1 m + fib'1 pn (* fib' n.-2 + fib' n.-1 *)
    end.

  Fixpoint loop m n k :=
    match k with
    | 0 => n
    | k.+1 => loop n (n + m) k
    end.
  Definition fib'2 n := loop 0 1 n.

  Compute fib'1 5.                           (* 8 *)
  Compute fib'2 5.                           (* 8 *)
  
(**
## idris の証明に近いもの
*)
  Lemma loop_is_like_fib' i j n :
    loop (i + j) (i + j + j) n = loop j (i + j) n + loop i j n.
  Proof.
    elim: n i j.
    - move=> i j.
      reflexivity.
    - move=> //= n IHn i j.
      Check IHn j (j + i)
        : loop (j + (j + i)) (j + (j + i) + (j + i)) n =
          loop (j + i) (j + (j + i)) n + loop j (j + i) n.
      rewrite [i + j]addnC.
      rewrite -[j + i + j]addnA [i + j]addnC.
      rewrite (IHn j (j + i)).
      reflexivity.
  Qed.
  
  Theorem two_fib'_eq' n : fib'2 n = fib'1 n.
  Proof.
    functional induction (fib'1 n).
    (* fib'2 0 = 1 *)
    - reflexivity.
    (* fib'2 1 = 1 *)
    - reflexivity.
    (* fib'2 m.+2 = fib'1 m + fib'1 m.+1 *)
    - rewrite /fib'2 [LHS]/=.
      rewrite [1 + 0]addnC.
      Check loop_is_like_fib' 0 1 m
        : loop (0 + 1) (0 + 1 + 1) m = loop 1 (0 + 1) m + loop 0 1 m.
      rewrite (loop_is_like_fib' 0 1 m).
      rewrite -IHn0.
      rewrite -IHn1.
      rewrite /fib'2 [RHS]/=.
      rewrite add0n addn0 [RHS]addnC.
      reflexivity.
  Qed.

(**
## Coq風の証明
*)  





