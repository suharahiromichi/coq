(**
TwoFibsEq 

https://zenn.dev/blackenedgold/books/introduction-to-idris

Chapter 23 依存型を使った定理証明入門
*)

From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.
Require Import FunInd.                      (* Functional Scheme *)
Require Import Recdef.                      (* Function *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
二種類の ffibonacci 数列の定義が同じことを示す。
 *)
Section Two_Fib_Eq.

(**
# fib の定義
*)
  Function fib1 (n : nat) : nat :=
    match n with
    | 0 => 0                                (* keen さんは 0 *)
    | 1 => 1
    | (m.+1 as pn).+1 => fib1 m + fib1 pn (* fib n.-2 + fib n.-1 *)
    end.

  Fixpoint loop m n k :=
    match k with
    | 0 => m                                (* keen さんは n *)
    | k.+1 => loop n (n + m) k
    end.
  Definition fib2 n := loop 0 1 n.

  Compute fib1 5.                           (* 5 *)
  Compute fib2 5.                           (* 5 *)
  
(**
## idris の証明に近いもの

- 補題
loopIsLikeFib : (i, j, n: Nat) -> loop (i + j) (i + j + j) n = (loop j (i + j) n) + (loop i j n)
loopIsLikeFib i j Z     = Refl
loopIsLikeFib i j (S k) =
  rewrite plusCommutative i j in
  rewrite plusCommutative (j + i) j in
  rewrite loopIsLikeFib j (j + i) k in
  Refl

-- 証明
twoFibEq : (n: Nat) -> fib2 n = fib1 n
twoFibEq Z         = Refl
twoFibEq (S Z)     = Refl
twoFibEq (S (S k)) =
  rewrite loopIsLikeFib 0 1 k in
  rewrite twoFibEq k in
  rewrite twoFibEq (S k) in
  Refl
*)
  Lemma loop_is_like_fib' i j n :
    loop (i + j) (i + j + j) n = loop j (i + j) n + loop i j n.
  Proof.
    elim: n i j.
    - move=> i j.
      rewrite addnC.            (* 定義の修正によって必要になった。 *)
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
  
  Theorem two_fib_eq' n : fib2 n = fib1 n.
  Proof.
    functional induction (fib1 n).
    (* fib2 0 = 1 *)
    - reflexivity.
    (* fib2 1 = 1 *)
    - reflexivity.
    (* fib2 m.+2 = fib1 m + fib1 m.+1 *)
    - rewrite /fib2 [LHS]/=.
      rewrite [1 + 0]addnC.
      Check loop_is_like_fib' 0 1 m
        : loop (0 + 1) (0 + 1 + 1) m = loop 1 (0 + 1) m + loop 0 1 m.
      rewrite (loop_is_like_fib' 0 1 m).
      rewrite -IHn0.
      rewrite -IHn1.
      rewrite /fib2 [RHS]/=.
      rewrite add0n addn0 [RHS]addnC.
      reflexivity.
  Qed.

(**
## Coq風の証明
*)  
  Lemma loop_is_like_fib i j n :
    loop (i + j) (i + j + j) n = loop j (i + j) n + loop i j n.
  Proof.
    elim: n i j => //= [| n IHn] i j.
    - by rewrite addnC.         (* 定義の修正によって必要になった。 *)
    - rewrite [i + j]addnC.
      rewrite -[j + i + j]addnA [i + j]addnC.
      by rewrite (IHn j (j + i)).
  Qed.
  
  Theorem two_fib_eq n : fib2 n = fib1 n.
  Proof.
    functional induction (fib1 n) => //.
    rewrite /fib2 [LHS]/=.
    rewrite (loop_is_like_fib 0 1 m).
    rewrite -IHn0.
    rewrite -IHn1.
    rewrite /fib2 [RHS]/=.
    by rewrite add0n addn0 [RHS]addnC.
  Qed.

End Two_Fib_Eq.

(* END *)

Check expnD
     : forall m n1 n2 : nat, m ^ (n1 + n2) = m ^ n1 * m ^ n2.

Lemma expn_twice: forall (k : nat), 2^k + 2^k = 2^(k+1).
Proof.
  move=> k.
  rewrite expnD expn1 muln2 -addnn.
  done.
Qed.
