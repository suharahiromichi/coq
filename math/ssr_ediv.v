(**
ユーグリッド除法 Euclidean division

========================

@suharahiromichi

2020/08/25
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import ssromega.                    (* ssromega タクティク *)
Require Import Recdef.                      (* Function コマンド *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)


(**
# ユーグリッド除法の一意性
*)
Lemma test2 (r1 r2 d : int) : 0 <= r1 < d ->
                              0 <= r2 < d ->
                              0 <= `| r1 - r2 | < d.
Proof.
  move/andP => [Hr1 Hr1d].
  move/andP => [Hr2 Hr2d].
  Search _ (`| _ - _ | < _).
  rewrite ltr_distl.
  apply/andP; split; [| apply/andP; split].
  - done.
  - rewrite ltr_subl_addr.
    Search _ (_ < _ + _).    
    Check ltr_paddl.
      by apply: ltr_paddl.
  - by apply: ltr_paddl.
Qed.

(*
    
    Check ltr_subl_addr.
    Check ltr_subr_addr.
    Check ltr_subl_addl.
    Check ltr_subr_addl.    
*)

Lemma test3 (x y : int) : `|x - y| = 0  <-> x = y.
Proof.
  split=> H.
  - apply: subr0_eq.
    move/normr0P in H.
      by move/eqP in H.
  - apply/normr0P.
    rewrite subr_eq0.
      by apply/eqP.
Qed.

(* D * Q = R *)
Lemma test' (d q r : int) : 0 <= r < `|d| -> q = (r %/ d)%Z -> q = 0.
Proof.
  move=> Hqd H.
  Check divz_small
    : forall (r : int_numDomainType) (d : int), 0 <= r < `|d|%N -> (r %/ d)%Z = 0.
  Check divz_small Hqd.
    by rewrite -(divz_small Hqd).
Qed.

Lemma test4 (x y : int) : `|x - y| = 0 -> x = y.
Proof.
  Search _ (`| _ | = 0).
  move/normr0P => H.
  Search _ (_ - _ == 0).
  rewrite subr_eq0 in H.
    by move/eqP in H.
Qed.

Lemma test5 q r d : 0 < d -> q * d = r -> q = (r %/ d)%Z.
Proof.
  move=> Hd H.
  apply/eqP.
Check eqz_div : forall (d : int_ZmodType) (m : int) (n : int_Ring),
       d != 0 -> (d %| m)%Z -> (n == (m %/ d)%Z) = (n * d == m).
  rewrite eqz_div.
  - by apply/eqP.
  - by move/lt0r_neq0 in Hd.
  - admit.                 (* (d %| r)%Z *)
    Compute (5 %| 0)%Z.    (* r は 0 になるので、成り立つわけだが。 *)
Admitted.

Goal forall r1 r2 q1 q2 d : int,
    0 < d ->
    0 <= r1 < `|d| ->
    0 <= r2 < `|d| ->
   `|q1 - q2| * d = `|r1 - r2| ->
                                (* `|q1 - q2| = (`|r1 - r2| %/ d)%Z -> *)
    q1 = q2.
Proof.
  move=> r1 r2 q1 q2 d Hd Hr1 Hr2.
  move=> Hdrq.
  move: (test2 Hr1 Hr2) => H.
  Check @test5 `|q1 - q2| `|r1 - r2| d Hd.
  move/(@test5 `|q1 - q2| `|r1 - r2| d Hd) in Hdrq.
  Check @test' d `|q1 - q2| `|r1 - r2| H.
  Check @test' d `|q1 - q2| `|r1 - r2| H Hdrq.
  move: (@test' d `|q1 - q2| `|r1 - r2| H Hdrq) => H1.
  apply: test4.
  done.
Qed.


Lemma test7 (x y : int) : `|x * y| = `|x| * `|y|.
Proof.
  case: x; case: y.
  done.
  admit.
  done.
  done.
  Check abszM : forall m1 m2 : int, `|(m1 * m2)%R|%N = (`|m1| * `|m2|)%N.
  Check abszM x y.
Admitted.

Lemma test6 (m d q1 q2 r1 r2 : int) : 0 < d ->
                                      m = q1 * d + r1 ->
                                      m = q2 * d + r2 ->
                                      (`|q1 - q2| * d)%Z = `|r1 - r2|.
Proof.
  move=> Hd H1 H2.
  rewrite H2 in H1.
  move=> {H2}.
  move/esym in H1.
  have H : q1 * d - q2 * d = r2 - r1 by admit.
  Search _ (_ - _ = _).
  Search _ (`| _ * _ |).
  Search _ (`| _ |).
  rewrite -[d]gtr0_norm //=.
  rewrite -test7.
  Search _ ((_ - _) * _).
  rewrite mulrBl.
  rewrite H.
  rewrite distrC.
  done.
Admitted.

Goal forall r1 r2 q1 q2 m d : int,
    0 < d ->
    0 <= r1 < `|d| ->
    0 <= r2 < `|d| ->
                   m = q1 * d + r1 ->
                   m = q2 * d + r2 ->
    q1 = q2.
Proof.
  move=> r1 r2 q1 q2 m d Hd Hr1 Hr2.
  move=> H1 H2.
  Check test6 Hd H1 H2.
  move: (test6 Hd H1 H2) => Hdrq.
  move: (test2 Hr1 Hr2) => H.
  Check @test5 `|q1 - q2| `|r1 - r2| d Hd.
  move/(@test5 `|q1 - q2| `|r1 - r2| d Hd) in Hdrq.
  Check @test' d `|q1 - q2| `|r1 - r2| H Hdrq.
  move: (@test' d `|q1 - q2| `|r1 - r2| H Hdrq) => H12.
  apply: test4.
  done.
Qed.

(* END *)

