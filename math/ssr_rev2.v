(**
二分割によるリストの反転
========================

@suharahiromichi

2020/04/19
 *)

From mathcomp Require Import all_ssreflect.
Require Import Recdef.
Require Import Wf_nat.                      (* well_founded lt *)
Require Import Program.Wf.                  (* Program Fixpoint *)
From common Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Rev2.
  
  Variable T : Type.

(**
## 例1 : リストのサイズを数値で別途与える。

n は size s と同じか、大きければよい。またsize sは2の冪でなくてもよい。
なぜなら、take と drop で結果が重ならないため。
 *)
  
(**
### 例11
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
      apply/ltP.                (* Coqの(<)をMathCompの(<)にする。 *)
      rewrite ltn_Pdiv //.
      (*
      move/negbT in Hn1.
      rewrite -ltnNge in Hn1.
        by apply: (@leq_ltn_trans 1 0).
       *)
        by ssromega.
    (* forall n : nat, seq T -> (n <= 1) = false -> (n %/ 2 < n)%coq_nat *)
    - move=> n HT Hn1.
      apply/ltP.                (* Coqの(<)をMathCompの(<)にする。 *)
      rewrite ltn_Pdiv //.
      (*
      move/negbT in Hn1.
      rewrite -ltnNge in Hn1.
        by apply: (@leq_ltn_trans 1 0).
       *)
        by ssromega.
    (* well_founded lt *)
    - by apply: lt_wf.                      (* Wf_nat *)
  Defined.
  
(**
### 例12

Program と if-then-else は併用できない。if条件が失われる。
そのため、match を使用する。match で数値で振り分ける場合。
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
      (* by apply/neq0_lt0n/negbTE/eqP/not_eq_sym. *)
      by ssromega.
  Qed.
  Obligation 2.
  Proof.
    apply/ltP/ltn_Pdiv => //.
    (* by apply/neq0_lt0n/negbTE/eqP/not_eq_sym. *)
      by ssromega.
  Qed.
  
(**
### 例13

Program と if-then-else は併用できない。if条件が失われる。
そのため、match を使用する。match でbool述語の真偽で振り分ける場合。
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
    move/eqP in n0.
    apply/ltP/ltn_Pdiv => //.
    (*
    rewrite -ltnNge in H.
    apply/neq0_lt0n/negbTE.
    rewrite -lt0n.
      by apply: (@leq_ltn_trans 1 0 n).
     *)
    by ssromega.
  Qed.
  Obligation 2.
  Proof.
    move/eqP in n0.
    apply/ltP/ltn_Pdiv => //.
    (*
    rewrite -ltnNge in H.
    apply/neq0_lt0n/negbTE.
    rewrite -lt0n.
      by apply: (@leq_ltn_trans 1 0 n).
     *)
    by ssromega.
  Qed.

(**
## 例2 : 再帰の回数を数値で指定する。

*)
  Lemma ltn_pred (n : nat) : 0 < n -> n.-1 < n.
  Proof.
    move=> Hn0.
    (* by rewrite prednK //. *)
      by ssromega.
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
### 例21
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
      apply/ltP.                (* Coqの(<)をMathCompの(<)にする。 *)
      rewrite ltn_pred //.
      move/negbT in Hn0.
        by rewrite -lt0n in Hn0.
    - move=> n HT Hn0.
      apply/ltP.                (* Coqの(<)をMathCompの(<)にする。 *)
      rewrite ltn_pred //.
      move/negbT in Hn0.
        by rewrite -lt0n in Hn0.
    (* well_founded lt *)
    - by apply: lt_wf.                      (* Wf_nat *)
  Defined.

(**
### 例22
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
    (*
    move/eqP in H.
    apply/ltP/ltn_pred.
      by rewrite lt0n negC.
     *)
      by ssromega.
  Qed.
  Obligation 2.
  Proof.
    (*
    move/eqP in H.
    apply/ltP/ltn_pred.
      by rewrite lt0n negC.
     *)
    by ssromega.
  Qed.
  
(**
### 例23
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
    move/eqP in n0.
    apply/ltP/ltn_pred.
    by rewrite lt0n.
  Qed.
  Obligation 2.
  Proof.
    move/eqP in n0.
    apply/ltP/ltn_pred.
    by rewrite lt0n.
  Qed.
  
(**
## 例3 : リストの長さ(size)を直接使用する。
*)
  Lemma take_size (n : nat) (s : seq T) : n < size s -> size (take n s) < size s.
  Proof.
    move=> H.
    rewrite size_takel //.
    by ssromega.
  Qed.
  
  Lemma drop_size (n : nat) (s : seq T) :
    0 < size s -> 0 < n -> size (drop n s) < size s.
  Proof.
    move=> Hs Hn.
    rewrite size_drop.
    (* rewrite -{2}[size s]subn0. *)
    by ssromega.
  Qed.
  
(**
### 例31

length は Coq、size は mathcomp である。
*)
  Function rev31 (s : seq T) {measure size s} : seq T :=
    if size s <= 1 then s
    else
      let s0 := take (size s %/ 2) s in
      let s1 := drop (size s %/ 2) s in
      rev31 s1 ++ rev31 s0.
  Proof.
    - move=> s Hs0.
      apply/ltP.                (* Coqの(<)をMathCompの(<)にする。 *)      
      apply: take_size.
      rewrite ltn_Pdiv //.
      (*
      move/negbT in Hs0.
      rewrite -ltnNge in Hs0.
        by apply: (@leq_ltn_trans 1 0).      
       *)
        by ssromega.
    - move=> s Hs0.
      apply/ltP.                (* Coqの(<)をMathCompの(<)にする。 *)      
      rewrite drop_size //.
      + by ssromega.
      + rewrite divn_gt0 //.
          by ssromega.
  Qed.
  
(**
### 例32
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
    - by ssromega.
    - rewrite divn_gt0 //.
        by ssromega.
  Qed.
  Obligation 2.
  Proof.
    apply/ltP/take_size.
    rewrite ltn_Pdiv //.
      by ssromega.
  Qed.
  
  (**
### 例33
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
    move/eqP in n.
    apply/ltP/drop_size.
    - by ssromega.
    - rewrite divn_gt0 //.
      by ssromega.
  Qed.
  Obligation 2.
  Proof.
    move/eqP in n.
    apply/ltP/take_size.
    rewrite ltn_Pdiv //.
    by ssromega.
  Qed.
  
End Rev2.

Definition data := [:: 0; 1; 2; 3; 4; 5; 6; 7].
Compute rev33 data.

Definition data16 := [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15].
Compute rev33 data16.

(* END *)
