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

Definition p10 : int := 10.                 (* Posz 10 *)
Definition m10 : int := - 10%:Z.            (* Negz 2 *)
Definition p3 : int := 3.                   (* Posz 3 *)
Definition m3 : int := - 3%:Z.              (* Negz 2 *)

(**
# ユーグリッド除法の定義
*)
Definition divz_floor (m d : int) : int := (`|m| %/ `|d|)%Z.
Compute divz_floor p10 p3.                  (* 3 *)

Definition divz_ceil (m d : int) : int :=
  if (d %| m)%Z then (`|m| %/ `|d|)%Z else (`|m| %/ `|d| + 1)%N.
Check divz_ceil : int -> int -> int.
Compute divz_ceil p3 p3.                    (* 1 *)
Compute divz_ceil p10 p3.                   (* 4 *)
Compute divz_ceil p10 m3.                   (* 4 *)
Compute divz_ceil m10 p3.                   (* 4 *)
Compute divz_ceil m10 m3.                   (* 4 *)

Lemma divz_floorp (m d : int) : d != 0 -> (divz_floor m d) * `|d| <= `|m|.
Proof.
Admitted.

Lemma divz_ceilp (m d : int) : d != 0 -> `|m| <= (divz_ceil m d) * `|d|.
Proof.
Admitted.


Definition edivz (m d : int) : int :=
  if (0 <= m) then
    sgz d * divz_floor m d
  else
    - sgz d * divz_ceil m d.

Definition emodz (m d : int) : int :=
  m - (edivz m d) * d.

Compute edivz p10 p3.                       (* 3 *)
Compute edivz p10 m3.                       (* -3 *)
Compute edivz m10 p3.                       (* -4 *)
Compute edivz m10 m3.                       (* 4 *)

Compute emodz p10 p3.                       (* 1 *)
Compute emodz p10 m3.                       (* 1 *)
Compute emodz m10 p3.                       (* 2 *)
Compute emodz m10 m3.                       (* 2 *)

(**
## 剰余が正であることの証明
*)
Lemma nge0_lt0 (m : int) : (0 <= m) = false -> m < 0.
Proof.
  move=> H.
  move/negbT in H.
  Search _ (~~ (_ <= _)).
  by rewrite -ltrNge in H.
Qed.

Lemma ltz_m_abs (m : int) : m < 0 -> m = - `|m|.
Proof.
  move=> H.
  rewrite ltr0_norm //=.
    by rewrite opprK.                            (* oppz ではない。 *)
Qed.

Lemma ediv_mod_ge0 (m d : int) : d != 0 -> 0 <= emodz m d.
Proof.
  move=> Hd.
  rewrite /emodz /edivz.
  case: ifP => H.
  - rewrite -mulrAC.
    Check abszEsg : forall m : int, `|m|%Z = sgz m * m.
    rewrite -abszEsg mulrC.
    rewrite subr_ge0.                       (* ssrnum *)
    Check normr_idP.
    move/normr_idP in H.
    rewrite -{2}H.
      (* (`|m| %/ `|d|)%Z * `|d|%N <= `|m| *)
      by apply: divz_floorp.

  (* m + - (- sgz d) * divz_ceil m d * d *)
  (* m + - - (sgz d * divz_ceil m d * d) *)      
  - rewrite !mulNr.
    rewrite [- - (sgz d * divz_ceil m d * d)]oppzK.
    rewrite -mulrAC.
    rewrite -abszEsg mulrC.
    move/nge0_lt0 in H.
    rewrite {1}(ltz_m_abs H).
    rewrite addrC subr_ge0.               (* addzC でない！ *)
      by apply: divz_ceilp.
Qed.

(**
# 一意性の証明
*)

Lemma test3 (x y : int) : (`|x - y| = 0)%N  <-> x = y.
Proof.
(*
  split=> H.
  - apply: subr0_eq.
    move/normr0P in H.
      by move/eqP in H.
  - apply/normr0P.
    rewrite subr_eq0.
      by apply/eqP.
Qed.
 *)
Admitted.

Lemma lemma1 (q d : nat) : (q * d < d)%N -> (q = 0)%N.
Proof.
Admitted.

Lemma lemma3 (q1 q2 r1 r2 d : int) :
  q1 * d + r1 = q2 * d + r2 -> (`|((q1 - q2) * d)%R|)%N = `|r1 - r2|%N.
Proof.
Admitted.

Lemma lemma2 (r1 r2 : int) (d : nat) :
  r1 < d -> r2 < d -> `|r1 - r2| < d.
Proof.
Admitted.

Lemma edivz_uniqness (r1 r2 q1 q2 m d : int) :
  0 <= r1 < `|d| ->
                 0 <= r2 < `|d| ->
                                m = q1 * d + r1 ->
                                m = q2 * d + r2 ->
                                q1 = q2.
Proof.
  move=> Hr1 Hr2 Hq1 Hq2.
  apply/test3.
  Check @lemma1 `|q1 - q2| `|d|.
  apply: (@lemma1 `|q1 - q2| `|d|).
  Check abszM.
  rewrite -abszM.
  rewrite Hq1 in Hq2.
  
  move/andP : Hr1 => [Hr1 Hr1d].
  move/andP : Hr2 => [Hr2 Hr2d].

  Check @lemma3 q1 q2 r1 r2 d.
  Check @lemma3 q1 q2 r1 r2 d Hq2.
  rewrite (@lemma3 q1 q2 r1 r2 d Hq2).

  apply: lemma2.
  - done.
  - done.
Qed.

(**
# MathComp での定義
 *)

Definition divz_d_K_n_absd (m d : int) :=
  let: (K, n) := match m with Posz n => (Posz, n) | Negz n => (Negz, n) end in
  (d, K, n, `|d|).


(*                                                  d  K      n |d| *)
Compute divz_d_K_n_absd p10 p3.             (*      3, Posz, 10, 3 *)
Compute divz_d_K_n_absd p10 m3.             (* Negz 2, Posz, 10, 3 *)
Compute divz_d_K_n_absd m10 p3.             (*      3, Negz,  9, 3 *)
Compute divz_d_K_n_absd m10 m3.             (* Negz 2, Negz,  9, 3 *)

Compute divz            p10 p3.             (* Posz 3 *)
Compute divz            p10 m3.             (* Negz 2 = -3 *)
Compute divz            m10 p3.             (* Negz 3 = -4 *)
Compute divz            m10 m3.             (* Posz 4 *)     

Compute (sgz (Posz 3)) * Posz (10 %/ 3).    (* Posz 3 *)
Compute (sgz (Negz 2)) * Posz (10 %/ 3).    (* Negz 2 = -3 *)
Compute (sgz (Posz 3)) * Negz ( 9 %/ 3).    (* Negz 3 = -4 *)
Compute (sgz (Negz 2)) * Negz ( 9 %/ 3).    (* Posz 4 *)

(* -1, 0, 1 を返す。 *)
Compute sgz (Negz 2)%R.                     (* Negz 0 (= -1) *)
Compute sgz (Posz 0)%R.                     (* Posz 0 *)
Compute sgz (Posz 3)%R.                     (* Posz 1 *)

Compute (Posz 1) * Posz (10 %/ 3).          (* Posz 3 *)
Compute (Negz 0) * Posz (10 %/ 3).          (* Negz 2 = -3 *)
Compute (Posz 1) * Negz ( 9 %/ 3).          (* Negz 3 = -4 *)
Compute (Negz 0) * Negz ( 9 %/ 3).          (* Posz 4 *)

Compute (Posz 1) * Posz 3.                  (* Posz 3 *)
Compute (Negz 0) * Posz 3.                  (* Negz 2 = -3 *)
Compute (Posz 1) * Negz 3.                  (* Negz 3 = -4 *)
Compute (Negz 0) * Negz 3.                  (* Posz 4 *)

(* Definition sgz x : int := if x == 0 then 0 else if x < 0 then -1 else 1. *)
Definition divz (m d : int) :=
  let: (K, n) := match m with Posz n => (Posz, n) | Negz n => (Negz, n) end in
  sgz d * K (n %/ `|d|)%N.
Definition modz (m d : int) : int := m - divz m d * d.

Compute divz            p10 p3.             (* Posz 3 *)
Compute divz            p10 m3.             (* Negz 2 = -3 *)
Compute divz            m10 p3.             (* Negz 3 = -4 *)
Compute divz            m10 m3.             (* Posz 4 *)     

Compute modz            p10 p3.             (* Posz 1 *)
Compute modz            p10 m3.             (* Posz 1 *)
Compute modz            m10 p3.             (* Posz 2 *)
Compute modz            m10 m3.             (* Posz 2 *)

(*
  m  =   q  *   d  + r
  10 =   3  *   3  + 1
  10 = (-3) * (-3) + 1
- 10 = (-4) *   3  + 2
- 10 =   4  * (-3) + 2
 *)

Definition divz' (m d : int) :=
  if (m >= 0) then
    sgz d * sgz m * (`|m| %/ `|d|)%N        (* floor *)
  else
    sgz d * sgz m *
    (if (`|d| %| `|m|)%N then (`|m| %/ `|d|)%N else (`|m| %/ `|d| + 1)%N). (* ceil *)
                                          
Check divz'.
Compute divz'           p10 p3.             (* Posz 3 *)
Compute divz'           p10 m3.             (* Negz 2 = -3 *)
Compute divz'           m10 p3.             (* Negz 3 = -4 *)
Compute divz'           m10 m3.             (* Posz 4 *)     


Definition p9 : int := 9.
Definition p8 : int := 8.   
Definition p7 : int := 7.
Definition p6 : int := 6.
Definition p5 : int := 5.    
Definition p4 : int := 4.
Definition p2 : int := 2.    
Definition p1 : int := 1.    

Definition m9 : int := - 9%:Z.
Definition m8 : int := - 8%:Z.
Definition m7 : int := - 7%:Z.
Definition m6 : int := - 6%:Z.
Definition m5 : int := - 5%:Z.
Definition m4 : int := - 4%:Z.
Definition m2 : int := - 2%:Z.
Definition m1 : int := - 1%:Z.


Compute divz' p9 p3.                        
Compute divz' p8 p3.                        
Compute divz' p7 p3.
Compute divz' p6 p3.
Compute divz' p5 p3.                        
Compute divz' p4 p3.
Compute divz' p3 p3.
Compute divz' p2 p3.                        

Compute divz' p9 m3.                        (* -3 *)
Compute divz' p8 m3.                        (* -2 *)
Compute divz' p7 m3.                        (* -2 *)
Compute divz' p6 m3.                        (* -2 *)
Compute divz' p5 m3.                        (* -1 *)
Compute divz' p4 m3.                        (* -1 *)
Compute divz' p3 m3.                        (* -1 *)
Compute divz' p2 m3.                        (* 0 *)

Compute divz' m9 p3.                        (* -3 *)
Compute divz' m8 p3.                        
Compute divz' m7 p3.
Compute divz' m6 p3.
Compute divz' m5 p3.                        (* -2 *)
Compute divz' m4 p3.
Compute divz' m3 p3.
Compute divz' m2 p3.                        (* -1 *)
Compute divz' m1 p3.                        (* -1 *)

Compute divz' m9 m3.                        (* -9 = 3 * -3  *)
Compute divz' m8 m3.                        (* -8 = 3 * -3 + 1 *)
Compute divz' m7 m3.
Compute divz' m6 m3.
Compute divz' m5 m3.                        (* -5 = 2 * -3 + 1 *)
Compute divz' m4 m3.
Compute divz' m3 m3.
Compute divz' m2 m3.                        (* -2 = 1 * -3 + 1 *)


(* END *)
