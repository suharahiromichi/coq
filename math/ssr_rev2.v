(**
�񕪊��ɂ�郊�X�g�̔��]
========================

@suharahiromichi

2020/04/19
 *)

From mathcomp Require Import all_ssreflect.
Require Import Recdef.
Require Import Wf_nat.                      (* well_founded lt *)
Require Import Program.Wf.                  (* Program Fixpoint *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Rev2.
  
  Variable T : Type.

(**
## ��1 : ���X�g�̃T�C�Y�𐔒l�ŕʓr�^����B

n �� size s �Ɠ������A�傫����΂悢�B�܂�size s��2�̙p�łȂ��Ă��悢�B
�Ȃ��Ȃ�Atake �� drop �Ō��ʂ��d�Ȃ�Ȃ����߁B
 *)
  
(**
### ��11
*)
  Function rev11 (n : nat) (s : seq T) {wf lt n} : seq T :=
    if n <= 1 then s
    else
      let n2 := n %/2 in
      let s0 := take n2 s in
      let s1 := drop n2 s in
      rev11 n2 s1 ++ rev11 n2 s0.
  Proof.
    (* forall n : nat, seq T -> (n <= 1) = false -> (n %/ 2 < n)%coq_nat *)
    - move=> n HT Hn1.
      apply/ltP.                (* aCoq��(<)��MathComp��(<)�ɂ���B *)
      apply: ltn_Pdiv => //.
      move/negbT in Hn1.
      rewrite -ltnNge in Hn1.
        by apply: (@leq_ltn_trans 1 0).
    (* forall n : nat, seq T -> (n <= 1) = false -> (n %/ 2 < n)%coq_nat *)
    - move=> n HT Hn1.
      apply/ltP.                (* aCoq��(<)��MathComp��(<)�ɂ���B *)
      apply: ltn_Pdiv => //.
      move/negbT in Hn1.
      rewrite -ltnNge in Hn1.
        by apply: (@leq_ltn_trans 1 0).
    (* well_founded lt *)
    - by apply: lt_wf.                      (* Wf_nat *)
  Defined.
  
(**
### ��12

Program �� if-then-else �͕��p�ł��Ȃ��Bif������������B
���̂��߁Amatch ���g�p����Bmatch �Ő��l�ŐU�蕪����ꍇ�B
*)
  Program Fixpoint rev12 (n : nat) (s : seq T) {wf lt n} : seq T :=
    match n with
    | 0 | 1 => s
    | _ => let n2 := n %/2 in
           let s0 := take n2 s in
           let s1 := drop n2 s in
           rev12 n2 s1 ++ rev12 n2 s0
    end.
  Obligation 1.
  Proof.
    apply/ltP/ltn_Pdiv => //.
      by apply/neq0_lt0n/negbTE/eqP/not_eq_sym.
  Qed.
  Obligation 2.
  Proof.
    apply/ltP/ltn_Pdiv => //.
      by apply/neq0_lt0n/negbTE/eqP/not_eq_sym.
  Qed.
  
(**
### ��13

Program �� if-then-else �͕��p�ł��Ȃ��Bif������������B
���̂��߁Amatch ���g�p����Bmatch ��bool�q��̐^�U�ŐU�蕪����ꍇ�B
*)
  Program Fixpoint rev13 (n : nat) (s : seq T) {wf lt n} : seq T :=
    match n <= 1 with
    | true => s
    | _ => let n2 := n %/2 in
           let s0 := take n2 s in
           let s1 := drop n2 s in
           rev13 n2 s1 ++ rev13 n2 s0
    end.
  Obligation 1.
  Proof.
    apply/ltP/ltn_Pdiv => //.
    move/eqP in H.
    rewrite -ltnNge in H.
    apply/neq0_lt0n/negbTE.
    rewrite -lt0n.
      by apply: (@leq_ltn_trans 1 0 n).
  Qed.
  Obligation 2.
  Proof.
    apply/ltP/ltn_Pdiv => //.
    move/eqP in H.
    rewrite -ltnNge in H.
    apply/neq0_lt0n/negbTE.
    rewrite -lt0n.
      by apply: (@leq_ltn_trans 1 0 n).
  Qed.

(**
## ��2 : �ċA�̉񐔂𐔒l�Ŏw�肷��B

*)
  Lemma ltn_pred (n : nat) : 0 < n -> n.-1 < n.
  Proof.
    move=> Hn0.
      by rewrite prednK //.
  Qed.

  Lemma negC (eT : eqType) (x y : eT) : (x != y) = (y != x).
  Proof.
    apply/idP/idP => H.
    - apply/eqP => H1.
      move/eqP in H.
        by apply: H.
    - apply/eqP => H1.
      move/eqP in H.
        by apply: H.
  Qed.
  
(**
### ��21
*)
  Function rev21 (n : nat) (s : seq T) {wf lt n} : seq T :=
    if n == 0 then s
    else
      let s0 := take (size s %/ 2) s in
      let s1 := drop (size s %/ 2) s in
      rev21 n.-1 s1 ++ rev21 n.-1 s0.
  Proof.
    (* forall n : nat, seq T -> (n == 0) = false -> (n.-1 < n)%coq_nat *)
    - move=> n HT Hn0.
      apply/ltP.                (* aCoq��(<)��MathComp��(<)�ɂ���B *)
      apply: ltn_pred.
      move/negbT in Hn0.
        by rewrite -lt0n in Hn0.
    - move=> n HT Hn0.
      apply/ltP.                (* aCoq��(<)��MathComp��(<)�ɂ���B *)
      apply: ltn_pred.
      move/negbT in Hn0.
        by rewrite -lt0n in Hn0.
    (* well_founded lt *)
    - by apply: lt_wf.                      (* Wf_nat *)
  Defined.

(**
### ��22
*)
  Program Fixpoint rev22 (n : nat) (s : seq T) {wf lt n} : seq T :=
    match n with
    | 0 => s
    | _ => let s0 := take (size s %/ 2) s in
           let s1 := drop (size s %/ 2) s in
           rev22 n.-1 s1 ++ rev22 n.-1 s0
    end.
  Obligation 1.
  Proof.
    move/eqP in H.
    apply/ltP/ltn_pred.
      by rewrite lt0n negC.
  Qed.
  Obligation 2.
  Proof.
    move/eqP in H.
    apply/ltP/ltn_pred.
      by rewrite lt0n negC.
  Qed.
  
(**
### ��23
*)
  Program Fixpoint rev23 (n : nat) (s : seq T) {wf lt n} : seq T :=
    match n == 0 with
    | true => s
    | _ => let s0 := take (size s %/ 2) s in
           let s1 := drop (size s %/ 2) s in
           rev23 n.-1 s1 ++ rev23 n.-1 s0
    end.
  Obligation 1.
  Proof.
    move/eqP in H.
    apply/ltP/ltn_pred.
      by rewrite lt0n.
  Qed.
  Obligation 2.
  Proof.
    move/eqP in H.
    apply/ltP/ltn_pred.
      by rewrite lt0n.
  Qed.

(**
## ��3 : ���X�g�̒���(size)�𒼐ڎg�p����B
*)
  
  Lemma take_size (n : nat) (s : seq T) : n < size s -> size (take n s) < size s.
  Proof.
    move=> H.
    rewrite size_takel //.
  Admitted.

  Lemma drop_size (n : nat) (s : seq T) :
    1 < size s -> 0 < n -> size (drop n s) < size s.
  Proof.
    move=> Hs Hn.
    rewrite size_drop.
    rewrite -{2}[size s]subn0.
(*
      by apply: (@ltn_sub2l (size s) 0 n).
*)
  Admitted.

(**
### ��31

length �� Coq�Asize �� mathcomp �ł���B
*)

  Function rev31 (s : seq T) {measure size s} : seq T :=
    if size s <= 1 then s
    else
      let s0 := take (size s %/ 2) s in
      let s1 := drop (size s %/ 2) s in
      rev31 s1 ++ rev31 s0.
  Proof.
    - move=> s Hs0.
      apply/ltP.                (* aCoq��(<)��MathComp��(<)�ɂ���B *)      
      apply: take_size.
      apply: ltn_Pdiv => //.
      move/negbT in Hs0.
      rewrite -ltnNge in Hs0.
        by apply: (@leq_ltn_trans 1 0).      
    - move=> s Hs0.
      apply/ltP.                (* aCoq��(<)��MathComp��(<)�ɂ���B *)      
      apply: drop_size.
      + move/negbT in Hs0.
          by rewrite -ltnNge in Hs0.
      + rewrite divn_gt0 //.
        Search _ ((_ <= _) = false).
  Admitted.

(**
### ��32
*)

    Program Fixpoint rev32 (s : seq T) {measure (size s)} : seq T :=
      match (size s) with
      | 0 => s
      | 1 => s
      | _ => let s0 := take (size s %/ 2) s in
             let s1 := drop (size s %/ 2) s in
             rev32 s1 ++ rev32 s0
      end.
    Obligation 1.
    Proof.
      apply/ltP/drop_size.
      admit.
    Admitted.
    Obligation 2.
    Proof.
      apply/ltP/take_size.
      admit.
    Admitted.

(**
### ��33
*)

    Program Fixpoint rev33 (s : seq T) {measure (size s)} : seq T :=
      match (size s <= 1) with
      | true => s
      | _ => let s0 := take (size s %/ 2) s in
             let s1 := drop (size s %/ 2) s in
             rev33 s1 ++ rev33 s0
      end.
    Obligation 1.
    Proof.
      apply/ltP/drop_size.
      admit.
    Admitted.
    Obligation 2.
    Proof.
      apply/ltP/take_size.
      admit.
    Admitted.
  
End Rev2.

Definition data := [:: 0; 1; 2; 3; 4; 5; 6; 7].
Compute rev33 data.

(* END *)
