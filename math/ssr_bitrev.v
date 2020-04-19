(**
ビット逆順に並び替え
========================

@suharahiromichi

2020/04/20
 *)

From mathcomp Require Import all_ssreflect.
Require Import Recdef.
Require Import Wf_nat.                      (* well_founded lt *)
Require Import Program.Wf.                  (* Program Fixpoint *)
Require Import ssr_omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section BitRev.
  
  Variable T : Type.
  
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
      by ssromega.
  Qed.
  
(**
### リストを反転する。

length は Coq、size は mathcomp である。
*)
  Program Fixpoint binrev (s : seq T) {measure (size s)} : seq T :=
    match (size s <= 1) with
    | true => s
    | _ => let s0 := take (size s %/ 2) s in
           let s1 := drop (size s %/ 2) s in
           binrev s1 ++ binrev s0
    end.
  Obligation 1.
  Proof.
    move/eqP in H.
    apply/ltP/drop_size.
    - by ssromega.
    - rewrite divn_gt0 //.
        by ssromega.
  Qed.
  Obligation 2.
  Proof.
    move/eqP in H.
    apply/ltP/take_size.
    rewrite ltn_Pdiv //.
      by ssromega.
  Qed.
  

(**
### リストをビット逆順にする
*)
  Fixpoint zip2 (s1 s2 : seq T) : seq T :=
    match s1, s2 with
    | [::], _ => [::]
    | _, [::] => [::]
    | c1 :: s1, c2 :: s2 => c1 :: c2 :: zip2 s1 s2
    end.
  Notation "s1 +++ s2" := (zip2 s1 s2) (right associativity, at level 60).

  Program Fixpoint bitrev (s : seq T) {measure (size s)} : seq T :=
    match (size s <= 1) with
    | true => s
    | _ => let s0 := take (size s %/ 2) s in
           let s1 := drop (size s %/ 2) s in
           bitrev s0 +++ bitrev s1
    end.
  Obligation 1.
  Proof.
    move/eqP in H.
    apply/ltP/take_size.
    rewrite ltn_Pdiv //.
      by ssromega.
  Qed.
  Obligation 2.
  Proof.
    move/eqP in H.
    apply/ltP/drop_size.
    - by ssromega.
    - rewrite divn_gt0 //.
        by ssromega.
  Qed.

End BitRev.

Definition data := [:: 0; 1; 2; 3; 4; 5; 6; 7].
Compute binrev data.               (* = [:: 7; 6; 5; 4; 3; 2; 1; 0] *)
Compute bitrev data.               (* = [:: 0; 4; 2; 6; 1; 5; 3; 7] *)

Definition data16 := [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15].
Compute binrev data16.
Compute bitrev data16.

(* END *)
