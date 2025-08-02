(**
自然数のルーラー関数
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssrZ zify ring lra.
(* opam install coq-equations *)
From Equations Require Import Equations.
Import Arith.                               (* Nat.land_spec *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section a.
  
(*Notation ".~ x" := (Nat.lnot x) (at level 35).*)
  Notation "x .& y" := (Nat.land x y) (at level 50).
  Notation "x .| y" := (Nat.lor x y) (at level 50).
  Notation "x .- y" := (Nat.ldiff x y) (at level 50).
  Notation "x .^ y" := (Nat.lxor x y) (at level 50).
  Notation "x .[ i ]" := (Nat.testbit x i).
  Notation "a ^^ b" := (xorb a b) (at level 50).

(**
# lxor を使って p を定義する。
 *)
  Definition px (n : nat) := n .^ n.-1.

  (* ``x & -x`` と違い、桁より右の桁がすべて1になる。 *)
  (* 自然数の範囲で計算できる。 *)
  Compute px 0.                             (* = 0x0000 *)
  Compute px 1.                             (* = 0x0001 *)
  Compute px 2.                             (* = 0x0011 *)
  Compute px 3.                             (* = 0x0001 *)
  Compute px 4.                             (* = 0x0111 *)
  Compute px 5.                             (* = 0x0001 *)
  Compute px 6.                             (* = 0x0011 *)
  Compute px 7.                             (* = 0x0001 *)
  Compute px 8.                             (* = 0x1111 *)
  
  Definition rulerx (n : nat) := Nat.log2 (px n).

  (* log2 をとると同じになる。 *)
  Compute rulerx 0.                         (* = 0 *)
  Compute rulerx 1.                         (* = 0 *)
  Compute rulerx 2.                         (* = 1 *)
  Compute rulerx 3.                         (* = 0 *)
  Compute rulerx 4.                         (* = 2 *)
  Compute rulerx 5.                         (* = 0 *)
  Compute rulerx 6.                         (* = 1 *)
  Compute rulerx 7.                         (* = 0 *)
  Compute rulerx 8.                         (* = 3 *)

(**
# ldiff を使って p を定義する。
*)
  Definition pd (n : nat) := n .- n.-1.

  (* ``x & -x`` 同様に変化した桁が1になる。 *)
  (* 自然数の範囲で計算できる。 *)
  Compute pd 0.                             (* = 0x0000 *)
  Compute pd 1.                             (* = 0x0001 *)
  Compute pd 2.                             (* = 0x0010 *)
  Compute pd 3.                             (* = 0x0001 *)
  Compute pd 4.                             (* = 0x0100 *)
  Compute pd 5.                             (* = 0x0001 *)
  Compute pd 6.                             (* = 0x0010 *)
  Compute pd 7.                             (* = 0x0001 *)
  Compute pd 8.                             (* = 0x1000 *)

  Lemma nat_ind2 :
    forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P (S (S n))) ->
      forall n : nat, P n.
  Proof.
    move=> P HP0 HP1 IH n.
    have H : (P n /\ P (S n)).
    - elim: n.
      + by split.
      + move=> n [] HPn HPsn.
        split=> //=.
        by apply: IH.
    - by case: H.
  Qed.
  
  Lemma coq_divn2 n : Nat.div2 n = n./2.
  Proof.
    elim/nat_ind2 : n => //= n IHn.
    by rewrite IHn.
  Qed.
  
  Lemma coq_evenP n : Nat.Even n <-> ~~ odd n.
  Proof.
    split => [/Nat.even_spec | H].
    - elim/nat_ind2 : n => [|| n IHn] //=.
      by rewrite negbK.
    - apply/Nat.even_spec.       
      elim/nat_ind2 : n H => [_ || n IHn] //=.
      by rewrite negbK.
  Qed.
  
  (* 補題：偶数+1 diff 偶数 = 1 *)
  Lemma ldiff_even_n_n1_diff_n__1 n : ~~ odd n -> n.+1 .- n = 1.
  Proof.
    move/even_halfK => <-.
    rewrite -muln2 mulnC -addn1.
    
    Check Nat.ldiff_odd_even n n
      : Nat.ldiff ((2 * n)%coq_nat + 1)%coq_nat (2 * n)%coq_nat = ((2 * Nat.ldiff n n)%coq_nat + 1)%coq_nat.
    
    rewrite Nat.ldiff_odd_even Nat.ldiff_diag.
    rewrite Nat.mul_0_r Nat.add_0_l.
    done.
  Qed.

  (* pd 関数の引数が 0 以外の偶数の場合、testbit_div2 のようなことになる。 *)
  Check Nat.testbit_div2 : forall a n : nat, (Nat.div2 a).[n] = a.[n.+1].
  
  Lemma doubleDiff (m n : nat) : (m .- n).*2 = m.*2 .- n.*2.
  Proof.
    have H x : x.*2 = (x * 2 ^ 1)%coq_nat by rewrite Nat.pow_1_r -muln2.
    rewrite 3!H.
    rewrite -3!Nat.shiftl_mul_pow2.
    by rewrite Nat.shiftl_ldiff.
  Qed.
  
  Lemma shiftr1_div2 (n : nat) : n./2 = Nat.shiftr n 1.
  Proof.
  Admitted.

  Lemma halfDiff (m n : nat) : (m .- n)./2 = m./2 .- n./2.
  Proof.
(*
    rewrite /Nat.ldiff.
    rewrite -!coq_divn2.
    rewrite -Nat.div2_bitwise.
    congr (_ (Nat.bitwise _ _ _ _)).
    Check m = (Nat.div2 m).+1. (* bitwise から余計な引数を渡しているため。 *)
    Restart.
*)
    have H x : x./2 = (x / 2 ^ 1)%coq_nat by rewrite Nat.pow_1_r -Nat.div2_div coq_divn2.
    rewrite 3!H.
    rewrite -3!Nat.shiftr_div_pow2.
    by rewrite Nat.shiftr_ldiff.
  Qed.
  
  Lemma pd_even (n i : nat) : (0 < n)%N -> ~~ odd n -> (pd n).[i.+1] = (pd n./2).[i].
  Proof.
    case: n => //= n _ Ho.
    rewrite /pd.
    rewrite -pred_Sn.
    rewrite negbK in Ho.
    (* rewrite Nat.testbit_div2. *)
    rewrite coq_divn2 halfDiff uphalfE.
    congr ((_ .- _) .[ _]).
    lia.
  Qed.
  
  Lemma pd_even' (n : nat) : (0 < n)%N -> ~~ odd n -> (pd n) = (pd n./2).*2.
  Proof.
    case: n => //= n _ Ho.
    rewrite /pd.
    rewrite -pred_Sn.
    rewrite negbK in Ho.
    (* rewrite Nat.testbit_div2. *)
    rewrite uphalfE doubleDiff.
    f_equal.
    - lia.
    - have -> : n.+1./2 = n./2.+1 by lia.   (* n は奇数 *)
      rewrite -pred_Sn.
      Check n = n./2.*2.                    (* n は奇数なので成り立たない。 *)
  Admitted.
  
  (* pd 関数の引数が奇数の場合、値は 1 である。 *)
  Lemma pd_odd__1 (n : nat) (i : nat) : odd n -> pd n = 1.
  Proof.
    case: n => //= n Hno.
    rewrite /pd -pred_Sn.
    by rewrite ldiff_even_n_n1_diff_n__1 //.
  Qed.
  
(**
# ルーラー関数
*) 
  Definition rulerd (n : nat) := Nat.log2 (pd n).

  (* log2 をとっても、同じである。 *)
  Compute rulerd 0.                         (* = 0 *)
  Compute rulerd 1.                         (* = 0 *)
  Compute rulerd 2.                         (* = 1 *)
  Compute rulerd 3.                         (* = 0 *)
  Compute rulerd 4.                         (* = 2 *)
  Compute rulerd 5.                         (* = 0 *)
  Compute rulerd 6.                         (* = 1 *)
  Compute rulerd 7.                         (* = 0 *)
  Compute rulerd 8.                         (* = 3 *)

(**
## ルーラー関数の性質
 *)
  
  Lemma rulerd_0 : rulerd 0 = 0.
  Proof.
    done.
  Qed.

  Lemma rulerd_odd (n : nat) : odd n -> rulerd n = 0.
  Proof.
    move=> Ho.
    by rewrite /rulerd pd_odd__1.
  Qed.
  
  Lemma rulerd_even (n : nat) : (0 < n)%N -> ~~ odd n -> rulerd n = (rulerd n./2).+1.
  Proof.
    move=> Hn He.
    rewrite /rulerd.
    rewrite -Nat.log2_double.
    - rewrite pd_even' => //.
      f_equal.
      lia.
    - rewrite /pd.
      Check 0 < n./2 .- n./2.-1.
      (* n は2以上だが、2のとき1になるので、成り立つはずである。 *)
  Admitted.

(**
# ルーラー関数の漸化式
*) 
  Equations ruler_rec (n : nat) : nat by wf n :=
    ruler_rec 0 => 0 ;
    ruler_rec n.+1 with odd n.+1 => {
      | true  => 0 ;
      | false => (ruler_rec n.+1./2).+1
      }.
  Obligation 1.
  apply/ltP.
  rewrite ltn_uphalf_double -muln2.
  by apply: ltn_Pmulr.
  Qed.

(**
## ruler_rec の定義から明らかな性質
*)
  Lemma ruler_rec_0 : ruler_rec 0 = 0.
  Proof.
    by simp ruler_rec.
  Qed.

  Lemma ruler_rec_odd (n : nat) : odd n -> ruler_rec n = 0.
  Proof.
    case: n => //= n Ho.
    simp ruler_rec.
    rewrite [odd n.+1]/= Ho.
    by rewrite ruler_rec_clause_2_equation_1.
  Qed.

  Lemma ruler_rec_even (n : nat) : (0 < n)%N -> ~~ odd n -> ruler_rec n = (ruler_rec n./2).+1.
  Proof.
    case: n => //= n Hn.
    rewrite negbK => He.
    simp ruler_rec => //=.
    rewrite He.
    rewrite ruler_rec_clause_2_equation_2 /=.
    done.
  Qed.

End a.

(* END *)
