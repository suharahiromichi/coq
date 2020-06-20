(**
数学ガールの秘密ノート

センター試験の数学的帰納法

https://cakes.mu/posts/1157


大学入試センター試験 : National Center Test for University Admissions

2013年大学入試センター試験 数学II・数学B 第3問（選択問題）(2)より 
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)
Require Import Program.Wf.                  (* Program wf *)
(* Import Program とすると、リストなど余計なものがついてくるので、Wfだけにする。 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(* 自然数を分母子とする分数を定義する。 *)

Section Fraction.

  Record fraction : Set :=
    Fraction {
        valq : (nat * nat);
        axiom : (0 < valq.2) && (coprime valq.1 valq.2)
      }.

  Canonical fraction_subType := Eval hnf in [subType for valq].
  Definition fraction_eqMixin := [eqMixin of fraction by <:].
  Canonical fraction_eqType := EqType fraction fraction_eqMixin.
  Definition fraction_choiceMixin := [choiceMixin of fraction by <:].
  Canonical fraction_choiceType := ChoiceType fraction fraction_choiceMixin.
  Definition fraction_countMixin := [countMixin of fraction by <:].
  Canonical fraction_countType := CountType fraction fraction_countMixin.
  Canonical fraction_subCountType := [subCountType of fraction].

  Definition fraq_fact (m d : nat) :=
    if (d == 0) then (0, 1) else (m %/ (gcdn m d), d %/ (gcdn m d)).
  
  Lemma fraq_subproof (x : (nat * nat)) :
    let: z := fraq_fact x.1 x.2 in
    (0 < z.2) && (coprime z.1 z.2).
  Proof.
    case: x => [m d].
    rewrite /fraq_fact.
    case: eqP => /eqP //= H.                (* H : d != 0 *)
    apply/andP.
    split.
    - admit.
    - admit.
  Admitted.
  
  Definition fraq (x : (nat * nat)) := @Fraction(_, _) (fraq_subproof x).
  
  Definition num (p : fraction) : nat := (valq p).1.
  Definition den (p : fraction) : nat := (valq p).2.

  Compute num (fraq (1, 2)).                (* 1 *)
  Compute den (fraq (1, 2)).                (* 2 *)
  
  Compute num (fraq (2, 4)).                (* 1 *)
  Compute den (fraq (2, 4)).                (* 2 *)
  
  
  (* 加算 *)
  
  Definition addq (p q : fraction) : fraction :=
    fraq ((num p) * (den q) + (den p) * (num q), den p * den q).
  
  Compute addq (fraq (2, 4)) (fraq (1, 2)). (* (1,1) *)

  Lemma addqC (p q : fraction) : addq p q = addq q p.
  Proof.
    rewrite /addq.
    rewrite [den q * den p]mulnC.
    rewrite [num q * den p + den q * num p]addnC.
    rewrite [den q * num p]mulnC.
    rewrite [num q * den p]mulnC.
    done.
  Qed.
  
  (* 通分・約分 *)
  Lemma num_den_fraq (p : fraction) : fraq (num p, den p) = p.
  Proof.
    (* eqType として一致すること。 *)
  Admitted.

  Lemma num_fraq (n d :  nat) : num (fraq (n, d)) = n %/ (gcdn n d).
  Proof.
  Admitted.

  Lemma den_fraq (n d :  nat) : den (fraq (n, d)) = d %/ (gcdn n d).
  Proof.
  Admitted.

  Lemma reduce_fraq_r (m n d : nat) : fraq (m * d, n * d) = fraq (m, n).
  Proof.
    (* eqType として一致すること。 *)
  Admitted.

  Lemma reduce_fraq_l (d m n : nat) : fraq (d * m, d * n) = fraq (m, n).
  Proof.
    (* eqType として一致すること。 *)
  Admitted.

  Lemma reduced_fraq_r (m n d : nat) : fraq (m %/ d, n %/ d) = fraq (m, n).
  Proof.
    (* eqType として一致すること。 *)
  Admitted.

  Lemma reduced_fraq_l (d m n : nat) : fraq (d %/ m, d %/ n) = fraq (m, n).
  Proof.
    (* eqType として一致すること。 *)
  Admitted.
  

  (* 乗算・除算 *)
  
  Definition mulq (p q : fraction) : fraction :=
    fraq (num p * num q, den p * den q).

  Compute mulq (fraq (4, 3)) (fraq (1, 2)). (* (2,3) *)
  
  Definition divq (p q : fraction) : fraction :=
    fraq (num p * den q, den p * num q).

  Compute divq (fraq (4, 3)) (fraq (2, 1)). (* (2,3) *)
  
  Lemma divqA (p q r : fraction) : divq p (divq q r) = (divq (mulq p r) q).
  Proof.
    rewrite /divq /mulq.
    rewrite !num_fraq !den_fraq.
    rewrite muln_divA; last by rewrite dvdn_gcdr.
    rewrite muln_divA; last by rewrite dvdn_gcdl.
    rewrite [(num p * num r) %/ gcdn (num p * num r) (den p * den r) * den q]mulnC.
    rewrite [(den p * den r) %/ gcdn (num p * num r) (den p * den r) * num q]mulnC.
    rewrite muln_divA; last by rewrite dvdn_gcdl.
    rewrite muln_divA; last by rewrite dvdn_gcdr.
    rewrite 2!reduced_fraq_r.
    rewrite !mulnA.
    rewrite [den q * num p in RHS]mulnC.
    rewrite [num q * den p in RHS]mulnC.
    done.
  Qed.
  
  Lemma mulKq (p q : fraction) : divq (mulq p q) p = q.
  Proof.
    rewrite /divq /mulq.
    rewrite num_fraq den_fraq.
    rewrite [(num p * num q) %/ gcdn (num p * num q) (den p * den q) * den p]mulnC.
    rewrite [(den p * den q) %/ gcdn (num p * num q) (den p * den q) * num p]mulnC.
    rewrite muln_divA; last by rewrite dvdn_gcdl.
    rewrite muln_divA; last by rewrite dvdn_gcdr.
    rewrite reduced_fraq_r.
    rewrite !mulnA.
    rewrite [den p * num p]mulnC.
    rewrite reduce_fraq_l.
      by rewrite num_den_fraq.
  Qed.
  
  Lemma divKq (p q : fraction) : divq p (divq p q) = q.
  Proof.
    by rewrite divqA mulKq.
  Qed.

End Fraction.

(* センターテスト問題 *)

Section Problem.

  (* 【２】の式 (a_k の定義) *)
  Function a (k : nat) {measure id k} : fraction :=
    match k with
    | 0 => fraq (3, 1)
    | 1 => fraq (3, 1)
    | 2 => fraq (3, 1)
    | k'.+3 => divq (addq (a k') (a k'.+1)) (a k'.+2)
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

  Definition b (k : nat) := a k.*2.
  Definition c (k : nat) := a k.*2.+1.

  Lemma lemma_1 (k : nat) :                 (* 計算で得た式(1) *)
    b k.+2 = divq (addq (c k) (b k.+1)) (c k.+1).
  Proof.
    rewrite /b !doubleS a_equation.
    rewrite /c doubleS.
    done.
  Qed.
  
  Lemma lemma_2 (k : nat) :                 (* 計算で得た式(2) *)
    c k.+1 = divq (addq (b k) (c k)) (b k.+1).
  Proof.
    rewrite /c !doubleS a_equation.
    rewrite /b doubleS.
    done.
  Qed.
  
  Lemma lemma_3 (k : nat) : b k = b k.+1.
  Proof.
    elim: k => [| k IHk] //=.
    rewrite lemma_1.
    rewrite lemma_2.
    rewrite -[in RHS]IHk.
    rewrite [addq (b k) (c k)]addqC.
    rewrite divKq.
    done.
  Qed.
  
  Goal forall k, b k = fraq (3, 1).         (* b の一般項 *)
  Proof.
    elim=> [| k IHk] //.
      by rewrite -lemma_3.
  Qed.
  
End Problem.

(* END *)
