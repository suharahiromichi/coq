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
  
  Definition num (z : fraction) : nat := (valq z).1.
  Definition den (z : fraction) : nat := (valq z).2.

  Compute num (fraq (1, 2)).                (* 1 *)
  Compute den (fraq (1, 2)).                (* 2 *)
  
  Compute num (fraq (2, 4)).                (* 1 *)
  Compute den (fraq (2, 4)).                (* 2 *)
  
  
  (* 加算 *)
  
  Definition addq (m n : fraction) : fraction :=
    fraq ((num m) * (den n) + (num n) * (den m), den m * den n).
  
  Compute addq (fraq (2, 4)) (fraq (1, 2)). (* (1,1) *)

  Lemma addqC (n m : fraction) : addq n m = addq m n.
  Proof.
    rewrite /addq.
    rewrite [den m * den n]mulnC.
    rewrite [num m * den n + num n * den m]addnC.
    done.
  Qed.
  
  (* 通分・約分 *)
  Lemma num_den_fraq (n : fraction) : fraq (num n, den n) = n.
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
  
  Definition mulq (m n : fraction) : fraction :=
    fraq ((num m) * (num n), (den m) * (den n)).

  Compute mulq (fraq (4, 3)) (fraq (1, 2)). (* (2,3) *)
  
  Definition divq (m n : fraction) : fraction :=
    fraq ((num m) * (den n), (den m) * (num n)).

  Compute divq (fraq (4, 3)) (fraq (2, 1)). (* (2,3) *)

  Lemma divqA (m n p : fraction) : divq m (divq n p) = (divq (mulq m p) n).
  Proof.
    rewrite /divq /mulq.
    rewrite !num_fraq !den_fraq.
    rewrite [(num m * num p) %/ gcdn (num m * num p) (den m * den p) * den n]mulnC.
    rewrite [(den m * den p) %/ gcdn (num m * num p) (den m * den p) * num n]mulnC.
    rewrite muln_divA; last by rewrite dvdn_gcdr.
    rewrite muln_divA; last by rewrite dvdn_gcdl.
    rewrite muln_divA; last by rewrite dvdn_gcdl.
    rewrite muln_divA; last by rewrite dvdn_gcdr.
    rewrite 2!reduced_fraq_r.
    rewrite !mulnA.
    rewrite [den n * num m in RHS]mulnC.
    rewrite [num n * den m in RHS]mulnC.
    done.
  Qed.
  
  Lemma mulKq (m d : fraction) : divq (mulq d m) d = m.
  Proof.
    rewrite /divq /mulq.
    rewrite num_fraq den_fraq.
    rewrite [(num d * num m) %/ gcdn (num d * num m) (den d * den m) * den d]mulnC.
    rewrite [(den d * den m) %/ gcdn (num d * num m) (den d * den m) * num d]mulnC.
    rewrite muln_divA; last by rewrite dvdn_gcdl.
    rewrite muln_divA; last by rewrite dvdn_gcdr.
    rewrite reduced_fraq_r.
    rewrite !mulnA.
    rewrite [num d * den d]mulnC.
    rewrite reduce_fraq_l.
      by rewrite num_den_fraq.
  Qed.

  Lemma divKq (m n : fraction) : divq m (divq m n) = n.
  Proof.
    by rewrite divqA mulKq.
  Qed.

End Fraction.

(* センターテスト問題 *)

Section Problem.

  Function a (n : nat) {measure id n} : fraction :=
    match n with
    | 0 => fraq (3, 1)
    | 1 => fraq (3, 1)
    | 2 => fraq (3, 1)
    | n'.+3 => divq (addq (a n') (a n'.+1)) (a n'.+2)
  end.
  - move=> n3 n2 n1 n Hn1 Hn2 Hn3.
      by ssromega.
  - move=> n3 n2 n1 n Hn1 Hn2 Hn3.
      by ssromega.
  - move=> n3 n2 n1 n Hn1 Hn2 Hn3.
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

  Definition b (n : nat) := a n.*2.
  Definition c (n : nat) := a n.*2.+1.

  Lemma lemma_b (k : nat) : b k.+2 = divq (addq (c k) (b k.+1)) (c k.+1).
  Proof.
    rewrite /b !doubleS a_equation.
    rewrite /c doubleS.
    done.
  Qed.
  
  Lemma lemma_c (k : nat) : c k.+1 = divq (addq (b k) (c k)) (b k.+1).
  Proof.
    rewrite /c !doubleS a_equation.
    rewrite /b doubleS.
    done.
  Qed.
  
  Goal forall k, b k = b k.+1.
  Proof.
    elim=> [| k IHk] //.
    rewrite lemma_b.
    rewrite lemma_c.
    rewrite -[in addq (c k) (b k.+1)]IHk.
    rewrite addqC.
    rewrite divKq.
    done.
  Qed.

End Problem.

(* END *)
