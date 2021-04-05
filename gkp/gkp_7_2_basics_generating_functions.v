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

(**
n < 0 の場合, f n = f0 とする。
n が負の部分が \Z に沸いて出るので、その分を加算しないといけない。

fib -1 = fib 0 = 0 なので問題ないのだが、ユニット関数 (n == 0) では成立しない。
*)  
  Axiom ztr_shift :
    forall f m, \Z_(n)(f (n - m))%N = z^m * \Z_(n)(f n) + (m * f 0%N)%:R.

(**
よく使う m = 1 のときを証明しておく。
*)
  Lemma ztr_shift1 f : \Z_(n)(f n.-1)%N = z * \Z_(n)(f n) + (f 0%N)%:R.
  Proof.
    have f_n_1 : forall (n : nat), (f n.-1 = f (n - 1))%N. move=> n; by rewrite subn1.
    rewrite (ztr_equal f_n_1).
    rewrite ztr_shift mul1n.
    done.
  Qed.

  Lemma ztr_shift2 f : \Z_(n)(f n.-2)%N = z^2 * \Z_(n)(f n) + (f 0%N).*2%:R.
  Proof.
    have f_n_2 : forall (n : nat), (f n.-2 = f (n - 2))%N. move=> n; by rewrite subn2.
    rewrite (ztr_equal f_n_2).
    rewrite -mul2n.
    rewrite ztr_shift.
    done.
  Qed.
  
  Lemma ztr_shift' f m : \Z_(n)(f (n - m))%N = z^m * \Z_(n)(f n) + (m * f 0%N)%:R.
  Proof.
(*
    elim: m {-2}m (leqnn m) => [m | n' IHn m] H.
    - have -> : (m = 0)%N by ssromega.
      rewrite expr0z mul1r mul0n addr0.
      have Hf0 : forall (n : nat), f n = f (n - 0)%N by move=> n; rewrite subn0.
        by rewrite -(ztr_equal Hf0).
    - Check IHn m.-1
      : (m.-1 <= n')%N ->
        \Z_ (n) f (n - m.-1)%N = z ^ m.-1 * \Z_ (n) f n + (m.-1 * f 0%N)%:R.
      Check ztr_shift1 f.
*)
    elim: m => [| m IHm].
    - admit.
    -
 (*   IHm : \Z_ (n) f (n - m)%N = z ^ m * \Z_ (n) f n + (m * f 0)%:R
  ============================
  \Z_ (n) f (n - m.+1)%N = z ^ m.+1 * \Z_ (n) f n + (m.+1 * f 0)%:R
 *)
  Admitted.

  Variable fib : nat -> nat.
  
  Compute (0.-1 <= 0)%N.                    (* true *)
  Compute (1.-1 <= 0)%N.                    (* true *)
  Compute (2.-1 <= 0)%N.                    (* false *)
  
  Lemma ztr_z : \Z_(n) (n.-1 <= 0)%N = z + 1.
  Proof.
    Check @ztr_shift1 (fun (n : nat) => n <= 0)%N.
    rewrite (@ztr_shift1 (fun (n : nat) => n <= 0)%N).
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
  
(**
フィボナッチ数列の一般項
*)
  Lemma fib0 : fib 0 = 0%N.
  Proof.
  Admitted.
  
  Lemma fibE' (n : nat) : fib n = (fib (n - 1) + fib (n - 2) + (n == 1))%N.
  Proof.
  Admitted.
  
  Lemma fibE (n : nat) : fib n = (fib n.-1 + fib n.-2 + (n == 1))%N.  
  Proof.
  Admitted.
  
(**
フィボナッチ数列の母関数
*)
  Definition G := \Z_(n) (fib n).

  Lemma fib_gen' : G = z * G + z^2 * G + z.
  Proof.
    rewrite /G.
    rewrite [LHS](ztr_equal fibE').
    rewrite 2!ztr_sum.
    rewrite !ztr_shift !fib0 !muln0.
    rewrite expr1z !addr0.
    rewrite ztr_z'.
    done.
  Qed.

  Lemma fib_gen'' : G = z * G + z^2 * G + z.
  Proof.
    rewrite /G.
    rewrite [LHS](ztr_equal fibE).
    rewrite 2!ztr_sum.
    rewrite ztr_shift1 fib0 addr0.
    rewrite ztr_shift2 fib0 -mul2n addr0.
    rewrite ztr_z'.
    done.
  Qed.
  
  Lemma fib_gen : G = 1 / (1 - z - z^2).
  Proof.
  Admitted.
  
End Basic_Maneuvers.

(* END *)
