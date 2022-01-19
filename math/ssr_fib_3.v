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

  Function fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.
  
  Fail Functional Scheme gcdn_ind := Induction for gcdn Sort Prop.
  (* Error: A fixpoint needs at least one parameter. *)
  
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
  Check gcd_ind
    : forall P : nat -> nat -> nat -> Prop,
      (forall m n : nat, m = 0 -> P 0 n n) ->
      (forall m n _x : nat,
          m = _x ->
          match _x with
          | 0 => False
          | _.+1 => True
          end -> P (n %% m) m (gcd (n %% m) m) -> P _x n (gcd (n %% m) m)) ->
      forall m n : nat, P m n (gcd m n).
  
  Lemma gcdC m n : gcd m n = gcd n m.
  Proof.
  Admitted.

  (* これは 1 <= m でないと証明できない。 *)
  (* ssr_fib_2.v fib_addition *)
  Lemma lemma5 m n :
    gcd (fib (n + m)) (fib n) = gcd (fib m) (fib n).
  Proof.
  Admitted.
  
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
  
  Lemma lemma9' (m n : nat) :
    (gcd (fib m) (fib n) = fib (gcd m n)).
  Proof.
    rewrite gcdC.
    functional induction (gcd m n).
    - rewrite gcdC.
        by rewrite gcd_equation.
    - rewrite lemma912'.
      done.
  Qed.
  
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
  
End Fib3.

(* END *)
