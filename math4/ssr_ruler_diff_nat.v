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

(**
## 補題
*)

(**
### 二つ飛びの帰納法
 *)
  Lemma nat_ind2 :
    forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P n.+2) ->
      forall n : nat, P n.
  Proof.
    move=> P HP0 HP1 IH n.
    have H : (P n /\ P n.+1).
    {
      elim : n => [| n [] HPn HPsn]; split => //=.
      by apply: IH.
    }.
    by case: H.
  Qed.
  
(**
### Coqのための補題
 *)
  Lemma coq_muln2 (n : nat) : (2 * n)%coq_nat = n.*2.
  Proof.
    lia.
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
  
(**
### 2で割る帰納法
 *)
  Lemma div2_lt : forall n, 2 <= n -> Nat.div2 n < n.
  Proof.
    intros n H.
    destruct n as [| [| n']]; simpl in *.
    - inversion H. (* n = 0 の場合 *)
    - inversion H. (* n = 1 の場合 *)
    - (* n >= 2 の場合 *)
      (* n = S (S n') *)
      rewrite -[_.+1]addn1 -[_.+2]addn1 leq_add2r.
      rewrite ltnS.
      apply/leP/Nat.div2_decr.
      lia.
  Qed.

  Definition div2_wf : well_founded (fun x y => Nat.div2 y = x /\ x < y).
  Proof.
    apply well_founded_lt_compat with (f := fun x => x).
    move=> x y [Heq Hlt].
    by apply/ltP.
  Qed.
  
  Lemma div2_ind :
    forall (P : nat -> Prop),
      P 0 ->
      P 1 ->
      (forall n, 1 < n -> P n./2 -> P n) ->
      forall n, P n.
  Proof.
    move=> P H0 H1 Hstep.
    apply: (well_founded_induction (well_founded_ltof _ (fun n => n))).
    case=> [| [| n'] IH] //=.
    apply: Hstep => //.
    apply: IH.
    rewrite /ltof.
    apply/ltP.
    rewrite -coq_divn2.
    by apply div2_lt.
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
  
  (* この補題は正しいが、この問題には適用できない。 *)
  (* 8 .- 7     = 8 *)
  (* と *)
  (* (4 .- 3)*2 = 4*2 *)
  (* が等しいのが、問題の趣旨だが、 *)
  (* この補題は、 *)
  (* 8 .- 6     = 8 *)
  (* であることを証明している。 *)
  Lemma doubleDiff (m n : nat) : (m .- n).*2 = m.*2 .- n.*2.
  Proof.
    have H x : x.*2 = (x * 2 ^ 1)%coq_nat by rewrite Nat.pow_1_r -muln2.
    rewrite 3!H.
    rewrite -3!Nat.shiftl_mul_pow2.
    by rewrite Nat.shiftl_ldiff.
  Qed.
  
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
  
  Lemma mul2K n : n.*2./2 = n.
  Proof.
    lia.
  Qed.

  Check Nat.bits_inj           (*  Numbers/Natural/Abstract/NBits.v *)
    : forall a b : nat, Nat.eqf (Nat.testbit a) (Nat.testbit b) -> a = b.
  Print Nat.eqf.
  (* = fun f g : nat -> bool => forall n : nat, f n = g n *)
  
  Lemma testbit_inj m n : (forall i, m.[i] = n.[i]) -> m = n.
  Proof.
    move=> H.
    by apply: Nat.bits_inj.
  Qed.
  
  (**
## p関数の性質
*)
  
  (**
### pd 関数の引数が奇数の場合、値は 1 である。
   *)
  Lemma pd_odd__1 (n : nat) (i : nat) : odd n -> pd n = 1.
  Proof.
    case: n => //= n Hno.
    rewrite /pd -pred_Sn.
    by rewrite ldiff_even_n_n1_diff_n__1 //.
  Qed.
  
  (**
### pd 関数の引数が偶数の場合、./2 した値から再帰的に求められる。testbit版
   *)
  Lemma pd_even_testbit (n i : nat) : (0 < n)%N -> ~~ odd n -> (pd n).[i.+1] = (pd n./2).[i].
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

  (* 似た補題 *)
  Lemma pd_even'_testbit (n i : nat) : (0 < n)%N -> (pd n.*2).[i.+1] = (pd n).[i].
  Proof.
    move=> Hn0.
    rewrite (@pd_even_testbit n.*2); try lia.
    by rewrite mul2K.
  Qed.
  
  (**
### pd 関数の引数が偶数の場合、./2 した値から再帰的に求められる。2倍版
   *)

  (* pd_even の証明では、doubleDiff 補題が使えそうだが、正しい証明にならない。
     なぜなら、= になるのは別な理由であるからだ。 *)
  (* その代わりに、testbit の単射性 testbit_inj を使う。 *)
  
  Check Nat.testbit_even_succ' : forall a i : nat, (2 * a)%coq_nat.[i.+1] = a.[i].
  
  Lemma pd_even_nm2_0bit n : (pd n.*2).[0] = false.
  Proof.
    rewrite /pd Nat.ldiff_spec /=.
    rewrite -coq_muln2 Nat.odd_even.
    done.
  Qed.
  
  Lemma pd_even_pm2_0bit n : (pd n).*2.[0] = false.
  Proof.
    rewrite /pd.
    rewrite -coq_muln2 Nat.testbit_even_0.
    done.
  Qed.
  
  Lemma pd_even_d2pm2_0bit n : (pd n./2).*2.[0] = false.
  Proof.
    rewrite /pd.
    rewrite -coq_muln2 Nat.testbit_even_0.
    done.
  Qed.

  Lemma pd_even_0bit n : ~~ odd n -> (pd n).[0] = false.
  Proof.
    move=> He.
    rewrite -[n in (pd n)]even_uphalfK //=.
    rewrite -Nat.bit0_odd.
    by rewrite pd_even_nm2_0bit.
  Qed.
  
  (* 苦労した補題 *)
  Lemma pd_even (n : nat) : (0 < n)%N -> ~~ odd n -> (pd n) = (pd n./2).*2.
  Proof.
(*
(* 間接証明 *)
    move=> Hn He.
    have := (@pd_even' n./2).
    rewrite even_halfK //=.
    have Hn2 : 0 < n./2 by lia.
    by move=> ->.
*)
    Restart.                                (* 直接証明 *)
    move=> Hn He.
    apply: testbit_inj => i.
    case: i => [| n']. (* i を 0 か 1以上で分ける。避けられないか？ *)
    - by rewrite pd_even_d2pm2_0bit pd_even_0bit.
    - rewrite -coq_muln2.
      rewrite Nat.testbit_even_succ'.
      by rewrite pd_even_testbit.
  Qed.

  (* 似た補題 *)
  Lemma pd_even' (n : nat) : (0 < n)%N -> (pd n.*2) = (pd n).*2.
  Proof.
    move=> Hn.
    apply: testbit_inj => i.
    case: i => [| n']. (* i を 0 か 1以上で分ける。避けられないか？ *)
    - by rewrite pd_even_nm2_0bit pd_even_pm2_0bit.
    - rewrite -[(pd n).*2]coq_muln2 //.
      rewrite Nat.testbit_even_succ'.
      by rewrite pd_even'_testbit.
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

  (**
### 補題
   *)
  (* 引数が1以上なら、値は1以上である。./2 による帰納法で求める。 *)
  Lemma pd_gt_0 n : 0 < n -> 0 < pd n.
  Proof.
    elim/div2_ind : n => //= n Hn1 IHn Hn.
    have := orbN (odd n).
    case/orP => Heo.
    (* n が奇数のとき、pd n = 1 *)
    - by rewrite pd_odd__1.
    (* n が偶数のとき、帰納法を使う。 *)
    - rewrite pd_even //=.
      rewrite double_gt0.
      apply: IHn.
      lia.
  Qed.
  
  Lemma pd_gt_0' n : 0 < n -> ~~ odd n -> 0 < pd n./2.
  Proof.
    move=> Hn He.
    Check @pd_gt_0 (n./2).
    rewrite (@pd_gt_0 (n./2)) //=.
    lia.
  Qed.
  
  (**
### 引数が0の時、値は0である。
  *)
  Lemma rulerd_0 : rulerd 0 = 0.
  Proof.
    done.
  Qed.

  (**
### 引数が奇数のとき、値は0である。
   *)
  Lemma rulerd_odd (n : nat) : odd n -> rulerd n = 0.
  Proof.
    move=> Ho.
    by rewrite /rulerd pd_odd__1.
  Qed.
  
  (**
### 引数が偶数のとき、./2の値から再帰的に求めることができる。
   *)
  Lemma rulerd_even (n : nat) : (0 < n)%N -> ~~ odd n -> rulerd n = (rulerd n./2).+1.
  Proof.
    move=> Hn He.
    rewrite /rulerd.
    rewrite -Nat.log2_double.
    - f_equal.                              (* log2 を消す。 *)
      rewrite coq_muln2.
      by rewrite pd_even.
    - apply/ltP.
      by rewrite pd_gt_0'.
  Qed.
  
  (* 似た補題 *)
  Lemma rulerd_even' (n : nat) : (0 < n)%N -> rulerd n.*2 = (rulerd n).+1.
  Proof.
    move=> Hn.
    rewrite /rulerd.
    rewrite -Nat.log2_double.
    - f_equal.                              (* log2 を消す。 *)
      rewrite coq_muln2.
      by rewrite pd_even'.
    - apply/ltP.
      by rewrite pd_gt_0.
  Qed.

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

ruleed の性質と対応している。
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

  Lemma ruler_rec_even' (n : nat) : (0 < n)%N -> ruler_rec n.*2 = (ruler_rec n).+1.
  Proof.
    move=> Hn.
    rewrite (@ruler_rec_even n.*2); try lia.
    - by rewrite mul2K.
  Qed.
  

(**
任意の n について、ruler_rec と rulerd が等しい。
*)
  Theorem ruler_rec__ruler'' n : ruler_rec n = rulerd n.
  Proof.
    elim/div2_ind : n => [| | n H1 IH].
    - by rewrite rulerd_0.
    - by rewrite rulerd_odd.
    - have := orbN (odd n).
      case/orP => Heo.
      + case: n H1 IH Heo.
        * by rewrite rulerd_0.
        * intros.
          rewrite rulerd_odd //=.
          by rewrite ruler_rec_odd.
      + rewrite rulerd_even; try lia.
        rewrite ruler_rec_even; try lia.
  Qed.
  
End a.

(* END *)
