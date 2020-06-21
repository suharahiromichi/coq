(**
数学ガールの秘密ノート、結城浩さん著

センター試験の数学的帰納法

https://cakes.mu/posts/1157


大学入試センター試験 : National Center Test for University Admissions

2013年大学入試センター試験 数学II・数学B 第3問（選択問題）(2)より 
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import ssromega.
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)
Require Import Program.Wf.                  (* Program wf *)
(* Import Program とすると、リストなど余計なものがついてくるので、Wfだけにする。 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(* 以下をインポートしてオープンすると、有理多項式が使えるようになる。 *)
(* ssralg.v *)
Import GRing.Theory.                 (* mulrNN を使えるようにする。 *)
(* ssrnum.v *)
Import Num.Theory.                   (* normr0_eq0 などを使えるようにする。 *)
(* ssrint.v *)
Import intZmod.                        (* addz など *)
Import intRing.                        (* mulz など *)
Import intOrdered.                     (* lez など *)
(* Open Scope int_scope. *)
(* Open Scope rat_scope. *)
Open Scope ring_scope.

(* ********** *)
(* # 有理数型 *)
(* ********** *)

Definition q1_3 := fracq (1%:Z, 3%:Z).      (* 1/3 *)
Definition q2_6 := fracq (2%:Z, 6%:Z).      (* 2/6 *)

(* 既約して得られる。 *)
Compute (valq q2_6).1.                      (* 1 *)
Compute (valq q2_6).2.                      (* 3 *)

Compute q1_3 == q2_6.                       (* true *)

Goal q1_3 = q2_6.
Proof.
  Fail reflexivity.                         (* = は成立しない。 *)
    by apply/eqP.                           (* == は成立する。 *)
Qed.


(* ## 有理数における (−a)(−b) = ab *)

Check rat_Ring : ringType.               (* rat_ringType ではない（注） *)
Check rat : Type.
Lemma rat_mulrNN (q1 q2 : rat) : - q1 * - q2 = q1 * q2.
Proof.
  (* 環一般に成り立つ補題 *)
  Check mulrNN : forall (R : ringType) (x y : R), (- x) *( - y) = x * y.
    by apply mulrNN.
Qed.

(*
(注) intとratは、命名規則を間違えている。

○int_eqType
×int_zmodType   ○int_ZmodType  
×rat_zmodType   ○rat_ZmodType  
○poly_zmodType                  

○int_eqType
×int_ringType   ○int_Ring      
×rat_ringType   ○rat_Ring      
○poly_ringType
*)

Section Lemmas.

  Lemma divqA (p q r : rat) : 0 < q -> 0 < r -> p / (q / r) = (p * r) / q.
  Proof.
    move=> Hq Hr.
    rewrite invrM.                 (* p * (r^-1^-1 / q) = p * r / q *)
    - rewrite invrK.               (* p * (r / q) = p * r / q *)
      rewrite -div1r.              (* p * (r * (1 / q)) = p * r * (1 / q) *)
      rewrite !mulrA.
      done.
    - by apply: unitf_gt0.                  (* q \is a GRing.unit *)
    - rewrite -invr_gt0 in Hr.             (* r^-1 \is a GRing.unit *)
        by apply: unitf_gt0.
  Qed.
  
  Lemma mulKq (p q : rat) : 0 < p -> (p * q) / p = q.
  Proof.
    move=> Hp.
    rewrite [p * q]mulrC.                   (* q * p / p = q *)
    (* rewrite -div1r. *)
    rewrite -mulrA.                         (* q * (p / p) = q *)
    (* rewrite div1r. *)
    rewrite divrr.                          (* q * 1 = q *)
    - by rewrite mulr1.
    - by rewrite unitf_gt0.                 (* p \is a GRing.unit *)
  Qed.
  
  Lemma divKq (p q : rat) : 0 < p -> 0 < q -> p / (p / q) = q.
  Proof.
    move=> Hp Hq.
    rewrite divqA; last done; last done.
    rewrite mulKq; last done.
    done.
Qed.

End Lemmas.


(* センターテスト問題 *)

Section Problem.

  (* 【２】の式 (a_k の定義) *)
  Function a (k : nat) {measure id k} : rat :=
    match k with
    | 0 => ratz 3                           (* fracq (3%:Z, 1%:Z) *)
    | 1 => ratz 3                           (* fracq (3%:Z, 1%:Z) *)
    | 2 => ratz 3                           (* fracq (3%:Z, 1%:Z) *)
    | k'.+3 => (a k' + a k'.+1) / a k'.+2
  end.
  - move=> k3 k2 k1 k Hk1 Hk2 Hk3.
      by ssromega.
  - move=> k3 k2 k1 k Hk1 Hk2 Hk3.
      by ssromega.
  - move=> k3 k2 k1 k Hk1 Hk2 Hk3.
      by ssromega.
  Defined.

  Compute a 0.                              (* (3, 1) *)
  Compute a 1.                              (* (3, 1) *)
  Compute a 2.                              (* (3, 1) *)
  Compute a 3.                              (* (2, 1) *)
  Compute a 4.                              (* (3, 1) *)
  Compute a 5.                              (* (5, 3) *)
  Compute a 6.                              (* (3, 1) *)
  Compute a 7.                              (* (14, 9) *)

  Definition b (k : nat) : rat := a k.*2.
  Definition c (k : nat) : rat := a k.*2.+1.

  Lemma lemma_1 (k : nat) :                 (* 計算で得た式(1) *)
    b k.+2 = (c k + b k.+1) / c k.+1.
  Proof.
    rewrite /b !doubleS a_equation.
    rewrite /c doubleS.
    done.
  Qed.
  
  Lemma lemma_2 (k : nat) :                 (* 計算で得た式(2) *)
    c k.+1 = (b k + c k) / b k.+1.
  Proof.
    rewrite /c !doubleS a_equation.
    rewrite /b doubleS.
    done.
  Qed.

  Lemma le0_eq0 (k : nat) : (k <= 0)%N = (k == 0)%N.
  Proof.
    rewrite leq_eqVlt ltn0 /=.
    by rewrite orbF.
  Qed.
  
  Lemma ak_gt_0 k : 0 < a k.
  Proof.
    elim: k {-2}k (leqnn k).                (* 完全帰納法のイデオム *)
    - move=> k.
      rewrite le0_eq0 => /eqP ->.
      done.
    - move=> n IHk.
      case => //.
      case => //.
      case => // k' Hk.
      rewrite a_equation.
      rewrite divr_gt0 //.
      + rewrite addr_gt0 //.
        * apply: IHk.
            by ssromega.
        * apply: IHk.
            by ssromega.
      + apply: IHk.
          by ssromega.
  Qed.
  
  Lemma bk_gt_0 k : 0 < b k.
  Proof.
    rewrite /b.
      by apply: ak_gt_0.
  Qed.
  
  Lemma ck_gt_0 k : 0 < c k.
  Proof.
    rewrite /c.
      by apply: ak_gt_0.
(*
    elim: k => //= k IHk.
    rewrite lemma_2.
    rewrite divr_gt0 //.
    - apply: addr_gt0.
      + by apply: bk_gt_0.
      + done.
    - by apply: bk_gt_0.
*)
  Qed.
  
  Lemma lemma_3 (k : nat) : b k = b k.+1.
  Proof.
    elim: k => [| k IHk] //.
    rewrite lemma_1.
    rewrite lemma_2.
    rewrite -[in RHS]IHk.
    rewrite [b k + c k]addqC.
    rewrite [RHS]divKq.
    - done.
    - apply: addr_gt0.
      + by apply: ck_gt_0.
      + by apply: bk_gt_0.
    - by apply: bk_gt_0.
  Qed.
  
  Goal forall k, b k = ratz 3.              (* b の一般項 *)
  Proof.
    elim=> [| k IHk] //.
      by rewrite -lemma_3.
  Qed.
  
End Problem.

(* END *)
