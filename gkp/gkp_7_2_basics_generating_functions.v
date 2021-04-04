(**
7.2 母関数の基本操作
========================

@suharahiromichi

2021_04_03
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import ssromega.                    (* ssromega タクティク *)
Require Import ssrinv.                      (* inv *)
Require Import Recdef.                      (* Function コマンド *)

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# nat で bool の補題
*)
Section BOOL_NAT.

(**
bool の and と nat の sub の関係
*)
  Lemma band_nsub (b1 b2 : bool) : (b1 && ~~b2) = (b1 - b2) :> nat.
  Proof.
    by case: b1; case: b2.
  Qed.
(*  
  Lemma band_1_0__1' (n : nat) : (n <= 1) && ~~(n <= 0) = (n == 1).
  Proof.
    apply/idP/idP.
    - move/andP => [H1 H2].
        by ssromega.
    - by move/eqP => ->.
  Qed.
  
  Lemma nsub_1_0__1' (n : nat) : ((n <= 1) - (n <= 0)) = (n == 1).
  Proof.
    rewrite -band_1_0__1'.
      by rewrite band_nsub.
  Qed.
*)
  Lemma band_1_0__1 (n : nat) : (n.-1 <= 0) && ~~(n <= 0) = (n == 1).
  Proof.
    apply/idP/idP.
    - move/andP => [H1 H2].
        by ssromega.
    - by move/eqP => ->.
  Qed.
  
  Lemma nsub_1_0__1 (n : nat) : ((n.-1 <= 0) - (n <= 0)) = (n == 1).
  Proof.
    rewrite -band_1_0__1.
      by rewrite band_nsub.
  Qed.

  Compute (0.-1 <= 0) - (0 <= 0).           (* 0 *)
  Compute (1.-1 <= 0) - (1 <= 0).           (* 1 *)
  Compute (2.-1 <= 0) - (2 <= 0).           (* 0 *)
  
End BOOL_NAT.
  
Open Scope ring_scope.                   (* %R を省略時解釈とする。 *)

Variable fT : fieldType.
Variable z : fT.
Variable Ztr : (nat -> nat) -> fT.
Notation "\Z_ ( n ) F" := (Ztr (fun n => F)) (at level 36).

Section TEST.
  
  Definition F1 (z : fT) : fT := 1 / (1 - z).
  Definition F2 (z : fT) : fT := 1 / (1 + z).
  
  Lemma test (z : fT) : F1 z * F2 z = 1 / (1 - z ^+ 2).
  Proof.
    rewrite /F1 /F2.
    rewrite mulf_div !mul1r.
    rewrite -subr_sqr expr1n.
    done.
  Qed.

End TEST.

(**
# 7.2 Basic Maneuvers 基本操作
*)
Section Basic_Maneuvers.

  Section TEST.
    Variables f g : nat -> nat.
    Check \Z_(n)(f n) : fT.
  End TEST.

(**
## 母関数への操作
*)  
  Axiom ztr_equal : forall f g, f =1 g -> \Z_(n)(f n) = \Z_(n)(g n).
(*
  Axiom ztr_unit : \Z_(n)(n == 0)%N = 1.
 *)
  Axiom ztr_unit : \Z_(n)(n <= 0)%N = 1.
  
  Axiom ztr_sum : forall f g, \Z_(n)(f n + g n)%N = \Z_(n)(f n) + \Z_(n)(g n).
  Axiom ztr_dif : forall f g, \Z_(n)(f n - g n)%N = \Z_(n)(f n) - \Z_(n)(g n).
  Axiom ztr_distl : forall a f, \Z_(n)(a * f n)%N = a%:R * \Z_(n)(f n).
  Axiom ztr_distr : forall f a, \Z_(n)(f n * a)%N = \Z_(n)(f n) * a%:R.
  
  (* f 0 = 0 の場合 *)
  Axiom ztr_shft1 : forall f, \Z_(n)(f n.-1)%N = z * \Z_(n)(f n).
  Axiom ztr_shft2 : forall f, \Z_(n)(f n.-2)%N = z^2 * \Z_(n)(f n).
  Axiom ztr_shft : forall f m, \Z_(n)(f (n - m))%N = z^m * \Z_(n)(f n).  
  
  (* f 0 <> 0 の場合？ *)
  Axiom ztr_shft1' : forall f, \Z_(n)(f n.-1)%N = (z + 1) * \Z_(n)(f n).

  Variable fib : nat -> nat.
  
  Compute (0.-1 <= 0)%N.                    (* true *)
  Compute (1.-1 <= 0)%N.                    (* true *)
  Compute (2.-1 <= 0)%N.                    (* false *)
  
  Lemma ztr_z : \Z_(n) (n.-1 <= 0)%N = z + 1.
  Proof.
    (* 公理を適当に増やすのは、お手盛りである。 *)
    Check @ztr_shft1' (fun (n : nat) => n <= 0)%N.     (* XXX *)
    rewrite (@ztr_shft1' (fun (n : nat) => n <= 0)%N). (* XXX *)
    rewrite ztr_unit.
      by rewrite mulr1.
  Qed.
  
  Lemma ztr_z' : \Z_(n) (n == 1)%N = z.
  Proof.
    Check ztr_equal nsub_1_0__1.
    rewrite -(ztr_equal nsub_1_0__1).
    rewrite ztr_dif.
    rewrite ztr_z.
    rewrite ztr_unit.
    rewrite -addrA.
    have H : 1 - 1 = 0.
    - move=> t.
      apply/eqP.
      by rewrite subr_eq add0r.
    - rewrite H addr0.
      done.
  Qed.
  
  Lemma fibE (n : nat) : fib n = (fib n.-1 + fib n.-2 + (n == 1))%N.
  Proof.
  Admitted.
  
  Definition G := \Z_(n) (fib n).

  Lemma fib_gen : G = z * G + z^2 * G + z.
  Proof.
    rewrite /G.
    rewrite [LHS](ztr_equal fibE).
    rewrite 2!ztr_sum.
    rewrite ztr_shft1 ztr_shft2.
    rewrite ztr_z'.
    done.
  Qed.
  
End Basic_Maneuvers.

(* END *)
