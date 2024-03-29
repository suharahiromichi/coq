(**
7.2 母関数の基本操作
========================

@suharahiromichi

2021_04_03
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From common Require Import ssromega.        (* ssromega タクティク *)
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
## bool の and と nat の sub の関係
*)
  Lemma band_nsub (b1 b2 : bool) : (b1 && ~~b2) = (b1 - b2) :> nat.
  Proof.
    by case: b1; case: b2.
  Qed.
  
(**
## n が 1 のときに 1 を返す ``n == 1`` 関数の定義
*)
  Lemma band_1_0__1' (n : nat) : (n <= 1) && ~~(n <= 0) = (n == 1).
  Proof.
    apply/idP/idP.
    - move/andP => [H1 H2].
      by ssromega.
    - by move/eqP => ->.
  Qed.
  
  Lemma band_1_0__1 (n : nat) : (n.-1 <= 0) && ~~(n <= 0) = (n == 1).
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
  
  Lemma nsub_1_0__1 (n : nat) : ((n.-1 <= 0) - (n <= 0)) = (n == 1).
  Proof.
    rewrite -band_1_0__1.
    by rewrite band_nsub.
  Qed.

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
## 母関数への操作（公理として与える）
*)  
  Axiom ztr_equal : forall f g, f =1 g -> \Z_(n)(f n) = \Z_(n)(g n).
  Axiom ztr_unit : \Z_(n)(n <= 0)%N = 1.
(**
``[n == 0]`` としてもよいが、``[-1 == 0]`` も成り立つので、誤解ないように上記の定義とする。
*)
  Axiom ztr_sum : forall f g, \Z_(n)(f n + g n)%N = \Z_(n)(f n) + \Z_(n)(g n).
  Axiom ztr_dif : forall f g, \Z_(n)(f n - g n)%N = \Z_(n)(f n) - \Z_(n)(g n).
  Axiom ztr_distl : forall a f, \Z_(n)(a * f n)%N = a%:R * \Z_(n)(f n).
  Axiom ztr_distr : forall f a, \Z_(n)(f n * a)%N = \Z_(n)(f n) * a%:R.
(**
``n < 0`` の場合, ``f n = f0`` とする。
n が負の部分が \Z に沸いて出るので、その分を加算しないといけない。

``fib -1 = fib 0 = 0`` なので問題ないのだが、ユニット関数 ``[n == 0]`` では成立しない。
*)  
  Axiom ztr_shift1 : forall f, \Z_(n)(f n.-1)%N = z * \Z_(n)(f n) + (f 0%N)%:R.
  
(**
1回シフトの式から、2回シフトの式を求めておく。
*)
  Lemma ztr_shift2 f : \Z_(n)(f n.-2)%N = z^2 * \Z_(n)(f n) + (z + 1) * (f 0%N)%:R.
  Proof.
    rewrite (ztr_shift1 (fun (n : nat) => f n.-1)) /=.
    rewrite ztr_shift1.
    rewrite mulrDr mulrA.                     (* 右辺 *)
    rewrite mulrDl addrA mul1r exprSz expr1z. (* 左辺 *)
    done.
  Qed.

(**
任意回のシフトの式は、以下の式になるが、Σの中に「体型」が書けないので、難しい。

``\Z_(n)(f (n - m)) = z^m * \Z_(n)(f n) + \sum_(0 <= i < m) z^m * (f 0)``
*)  

(**
## ``n = 1`` のときだけ 1 になる関数
*)
  Compute (0.-1 <= 0)%N.                    (* true *)
  Compute (1.-1 <= 0)%N.                    (* true *)
  Compute (2.-1 <= 0)%N.                    (* false *)
  
  Compute ((0.-1 <= 0) - (0 <= 0))%N.       (* 0 *)
  Compute ((1.-1 <= 0) - (1 <= 0))%N.       (* 1 *)
  Compute ((2.-1 <= 0) - (2 <= 0))%N.       (* 0 *)
  
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
## フィボナッチ数列の一般項
*)
  Fixpoint fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (ppn.+1 as pn).+1 => fib ppn + fib pn (* fib n.-2 + fib n.-1 *)
    end.
(*
  Variable fib : nat -> nat.
 *)
  
  Lemma fib0 : fib 0 = 0%N.
  Proof.
    done.
  Qed.
  
  Lemma fib_n n : fib n.+2 = (fib n + fib n.+1)%N.
  Proof.
    done.
  Qed.
  
  Lemma fibE (n : nat) : fib n = (fib n.-1 + fib n.-2 + (n == 1))%N.  
  Proof.
    case: n => [| n] //.                    (* fib 0 *)
    case: n => [| n] //.                    (* fib 1 *)
    have -> : n.+2.-1 = n.+1 by done.
    have -> : n.+1.-1 = n by done.
    have -> : (n.+2 == 1%N) = false by done.
    rewrite fib_n addn0 addnC.              (* fib 2 *)
    done.
  Qed.
  
  (**
## フィボナッチ数列の母関数
*)
  Definition G := \Z_(n) (fib n).

  Lemma fib_gen' : G = z * G + z^2 * G + z.
  Proof.
    rewrite /G.
    rewrite [LHS](ztr_equal fibE).
    rewrite 2!ztr_sum.
    rewrite ztr_shift1 fib0 addr0.
    rewrite ztr_shift2.
    rewrite fib0 mulr0 addr0.
    rewrite ztr_z'.
    done.
  Qed.
  
  Lemma l_a_a_0 (a : fT) : -a + a = 0.
  Proof.
    rewrite addrC.
    rewrite -[LHS]add0r addrA.
    rewrite addrK.
    done.
  Qed.
  
  (* z を含む式は 0 ではない。 *)
  Axiom l_z_z2_n_0 : 1 - z - z ^ 2 != 0.
  
  Lemma fib_gen : G = z / (1 - z - z^2).
  Proof.
    rewrite -[LHS]mulr1.
    rewrite -[in LHS](mulfV l_z_z2_n_0).
    rewrite [LHS]mulrA.                     (* 「/」 にも使える。 *)
    congr (_ / _).
    rewrite mulrC.
    rewrite 2!mulrBl mul1r.
    rewrite {1}fib_gen'.
    rewrite [_ - z * G]addrC ?addrA.    (* - z * G を先頭にする。 *)
    rewrite l_a_a_0 add0r.              (* 相殺する。 *)
    rewrite [_ - z^2 * G]addrC ?addrA.  (* - z^2 * G を先頭にする。 *)
    rewrite l_a_a_0 add0r.              (* 相殺する。 *)
    done.
  Qed.

End Basic_Maneuvers.

(**
## 任意回数のシフト
*)
Section Shift.

(*
  Definition zs (m : nat) :=
    foldr (@GRing.add fT) 1 (map (exprz z \o Posz) (iota 1 m)).
 *)

  Fixpoint zs (m : nat) : fT :=
    match m with
    | 0 => 1
    | m.+1 => 1 + z * (zs m)
    end.
  Notation "z^^ m" := (zs m) (at level 30, right associativity).
  
  Goal z^^0 = 1.
  Proof.
    rewrite /zs.
    done.
  Qed.
  
  Goal z^^1 = 1 + z.
  Proof.
    rewrite /zs.
    rewrite mulr1.
    done.
  Qed.

  Goal z^^2 = 1 + z + z^2.
  Proof.
    rewrite /zs.
    rewrite mulr1 mulrDr mulr1 addrA.
    rewrite exprSz expr1z.
    done.
  Qed.
  
  Goal 1 + z * z^^3 = z^^4.
  Proof.
    rewrite /zs.
    done.
  Qed.
  
  Lemma ez_shift (m : nat) : 1 + z * z^^m = z^^m.+1.
  Proof.
    done.
  Qed.
  
  Lemma ztr_shift f m :
    \Z_(n)(f (n - m.+1)%N) = z^m.+1 * \Z_(n)(f n) + z^^m * (f 0%N)%:R.
  Proof.
    elim: m.
    - rewrite /= mul1r expr1z.
      have H : forall n, f (n - 1)%N = f n.-1.
      + move=> n.
        by rewrite subn1.
      + rewrite (ztr_equal H).
        rewrite -ztr_shift1.
        done.
    - move=> /= m IHm.
      rewrite exprSz mulrDl mul1r addrCA -2!mulrA -mulrDr addrC.
      rewrite -IHm.
      have H1 : forall n, f (n - m.+2)%N = f ((n - m.+1).-1)%N.
      + move=> n.
        f_equal.
        by ssromega.
      have H2 : forall n, f (n.-1 - m.+1)%N = f (n - m.+1).-1%N.
      + move=> n.
        f_equal.
        by ssromega.
      + rewrite (ztr_equal H1).
        rewrite -(ztr_equal H2).
        rewrite -(ztr_shift1 (fun (n : nat) => f (n - m.+1)%N)).
        done.
  Qed.
  
  Lemma ztr_shift' f m :
    (1 <= m)%N ->
    \Z_(n)(f (n - m)%N) = z^m * \Z_(n)(f n) + z^^m.-1 * (f 0%N)%:R.
  Proof.
    move=> Hm.
    have H : forall n, f (n - m)%N = f (n - m.-1.+1)%N.
    - move=> n.
      f_equal.
      by ssromega.
    - rewrite (ztr_equal H).
      rewrite (ztr_shift f m.-1%N).
      by rewrite prednK.
  Qed.

End Shift.

(* END *)
