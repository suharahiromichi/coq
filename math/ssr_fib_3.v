(**
フィボナッチ数の最大公約数

GCD of Fibonacci Numbers
*)
From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import FunInd.                      (* Functional Scheme *)
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Fib3.

(**  
# フィボナッチ数の定義と定理
*)
  Function fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.
  
  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.

  Lemma lemma3 (n : nat) : coprime (fib n) (fib n.+1).
  Proof.
    rewrite /coprime.
    elim: n => [//= | n IHn].
    rewrite fib_n.
      by rewrite gcdnDr gcdnC.
  Qed.
  
(**
フィボナッチ数列の加法定理
*)
  Lemma fib_addition n m :
    1 <= m -> fib (n + m) = fib m * fib n.+1 + fib m.-1 * fib n.
  Proof.
    (* see. ssr_fib_2.v *)
  Admitted.                                 (* OK *)

(**
# GCDの定義と定理
*)  
  Fail Functional Scheme gcdn_ind := Induction for gcdn Sort Prop.
  (* Error: A fixpoint needs at least one parameter. *)
  
(**
仕方ないので Function を使って自分で定義する。
*)
  Function gcd (m n : nat) {wf lt m} : nat :=
    match m with
    | 0 => n
    | _ => gcd (n %% m) m
    end.
  Proof.
    - move=> m n m0 _.
      apply/ltP.
        by rewrite ltn_mod.
    - by apply: lt_wf.
  Qed.

(**
MathComp の gcdn を同じであることを証明する。
*)  
  Lemma gcdE m n : gcdn m n = gcd m n.
  Proof.
    functional induction (gcd m n).
    - by rewrite gcd0n.
    - rewrite -IHn0.
        by rewrite gcdnC gcdn_modl.
  Qed.
  
  Check gcdnC : forall m n, gcdn m n = gcdn n m.
  Lemma gcdC m n : gcd m n = gcd n m.
  Proof.
      by rewrite -2!gcdE gcdnC.
  Qed.
  
  Lemma gcd0m m : gcd 0 m = m.
  Proof.
      by rewrite gcd_equation.
  Qed.
  
  Lemma gcdmm m : gcd m m = m.
  Proof.
    case: m => [| m].
    - by rewrite gcd_equation.
    - rewrite gcd_equation.
      have -> : m.+1 %% m.+1 = 0 by rewrite modnn.
        by rewrite gcd0m.
  Qed.
  
  Lemma lemma5'' n : gcd n n = gcd 0 n.
  Proof.
      by rewrite gcdmm gcd0m.
  Qed.
  
  Check gcdnMDl : forall k m n : nat, gcdn m (k * m + n) = gcdn m n.
  Lemma gcdMDl (k m n : nat) : gcd m (k * m + n) = gcd m n.
  Proof.
      by rewrite -2!gcdE gcdnMDl.
  Qed.
  
  Check Gauss_gcdl : forall p m n : nat, coprime p n -> gcdn p (m * n) = gcdn p m.
  Lemma Gauss_gcdl' p m n : coprime p n -> gcd p (m * n) = gcd p m.
  Proof.
    rewrite -2!gcdE.
      by apply: Gauss_gcdl.
  Qed.
  
(**
# フィボナッチ数のGCD
*)
  Lemma lemma5' m n :
    1 <= m -> gcd (fib (n + m)) (fib n) = gcd (fib m) (fib n).
  Proof.
    move=> H.
    rewrite fib_addition //.
    rewrite gcdC addnC gcdMDl.
    rewrite Gauss_gcdl'.
    - by rewrite gcdC.
    - by apply: lemma3.
  Qed.
  
  Lemma lemma5 m n :
    gcd (fib (n + m)) (fib n) = gcd (fib m) (fib n).
  Proof.
    case: m => [| m].
    - rewrite addn0 /=.
        by apply: lemma5''.
    - rewrite lemma5' //=.
  Qed.
  
  Lemma lemma912'' n q r :
    gcd (fib (q * n + r)) (fib n) = gcd (fib n) (fib r).
  Proof.
    elim: q => [| q IHq].
    - rewrite mul0n add0n.
      rewrite gcdC.
      done.
    - Search _ (_.+1 * _).
      rewrite mulSn -addnA.
      rewrite [LHS]lemma5.
      done.
  Qed.
  
  Lemma lemma912' m n :
    gcd (fib m) (fib n) = gcd (fib n) (fib (m %% n)).
  Proof.
    move: (lemma912'' n (m %/ n) (m %% n)).
    rewrite -divn_eq.
    done.
  Qed.

(**
# 証明したいもの
*)
  Compute gcdn 0 0.                         (* 0 *)
  Compute gcdn 1 0.                         (* 1 *)
  Compute gcdn 0 1.                         (* 1 *)
  Compute gcdn 1 1.                         (* 1 *)
  
  Goal gcd (fib 1) (fib 0) = fib (gcd 1 0).
  Proof.
    rewrite gcd_equation.
    simpl.
    rewrite gcd_equation.
    simpl.
    done.
  Qed.
  
  Lemma lemma9' (m n : nat) :
    (gcd (fib m) (fib n) = fib (gcd m n)).
  Proof.
    rewrite gcdC.
    functional induction (gcd m n).
    - rewrite gcdC.
      rewrite gcd_equation.
      done.
    (* 
  IHn0 : gcd (fib m) (fib (n %% m)) = fib (gcd (n %% m) m)
  ============================
  gcd (fib n) (fib m) = fib (gcd (n %% m) m)
     *)
    - rewrite lemma912'.
      done.
  Qed.
  
End Fib3.

(**
GCDの帰納法の証明
*)
Section Fib31.

  Lemma gcdn_ind : forall P : nat -> nat -> nat -> Prop,
    (forall m n : nat, m = 0 -> P 0 n n) ->
    (forall m n : nat,
          match m with
          | 0 => False
          | _.+1 => True
          end -> P (n %% m) m (gcdn (n %% m) m) -> P m n (gcdn (n %% m) m)) ->
    forall m n : nat, P m n (gcdn m n).
  Proof.
    move=> P H1 H2 m n.
    rewrite gcdnE /=.
    elim: n.
    - case: m => //=.
      + by apply: H1.
      + move=> n.
        rewrite mod0n gcd0n.
        admit.
    - case: m.
      + move=> n //= H.
          by apply: H1.
      + move=> n n'.
        case H : n.+1 => //=.
        rewrite -H.
        move=> Hc.
        apply: H2 => //.
  Admitted.
  
End Fib31.

(* END *)
