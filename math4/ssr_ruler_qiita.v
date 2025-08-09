(**
ルーラー関数とそのの漸化式について
=========================
2025/08/10      @suharahiromichi

# はじめに

結城浩さんの「数学ガールの秘密ノート／ビットとバイナリ」[1]では、
ビット演算、すなわち、整数や自然数 (注1) を2進表現したときの桁どうしの演算を取り上げています。

ビット演算は、通常、2進4桁とか8桁とか32桁とかの有限の範囲で考えることが多く、[1]でも同様ですが (注2)
今回は、整数や自然数の範囲で考えてみたいと思います。

ご注意：この記事は、[1]のネタバレ、および、演習問題の解答を含みます。
*)

(**
# 問題

(1) ``n & -n`` は何を意味するか。ただし、``n``は1以上の自然数、``&``はビット毎の論理積、``-``は負号（2の補数）とする。

(2) ``log2 (n & -n)`` がルーラー関数 (Ruler function [2]) であることを示す。ただし、``log2``は 2を底とする対数とする。

(3) ルーラー関数の漸化式を定義し、(2)と等しいことを証明する。


ルーラー関数というのは``n``を2進表現したときの「最も右側の``1``の桁数、ただし0桁目から数える」を返す関数です。
例えば、n = 6 = 0110 なので、n=6のルーラー関数は1 となります。ちょっと計算してみると、次のようになります。

| n | n    | -n    | n & -n | log2 (n & -n)  |
|:-:|:----:|:-----:|:------:|:-------------:|
| 1 | 00001 | 11111  | 00001   | 0     |
| 2 | 00010 | 11110  | 00010   | 1     |
| 3 | 00011 | 11101  | 00001   | 0     |
| 4 | 00100 | 11100  | 00100   | 2     |
| 5 | 00101 | 11011  | 00001   | 0     |
| 6 | 00110 | 11010  | 00010   | 1     |
| 7 | 00111 | 11001  | 00001   | 0     |
| 9 | 01000 | 11000  | 01000   | 3     |

本記事では、(3)を形式化して証明する過程で、(1)や(2)を明らかにしていきます。
 *)

(**
# 証明の方針
*)

(**
# 証明の道具立て

使い慣れているので MathComp を使いますが、MathComp ではビット演算が用意されていないので、
自然数のビット演算は、Standard Rocq のライブラリ (Arith) をインポートして使います。
MathComp の nat と Standard Rocq の Nat の自然数の定義は同じなので、概ね互換性があります。
わずかな非互換の箇所については説明します。

整数については、Standard Rocq の 整数 Z (ZArith) は使わず、MathComp の int の上で独自に定義します。
このとき Lean/Math4 を参考にします。Lean の定義のほうが、MathComp に近いからです。

これとは別に、関数の定義には Rocq の Equations を使用します。
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ssrZ zify ring lra.
(* opam install coq-equations *)
From Equations Require Import Equations.
Import Arith.                               (* Nat.land_spec *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.                        (* ssralg.v *)
Import Num.Def Num.Theory.                  (* ssrnum.v *)
Import intZmod.

(**
# ビット演算の定義

##  自然数のビット演算の演算子の定義
*)
Notation "x .& y" := (Nat.land x y) (at level 50) : nat_scope.
Notation "x .| y" := (Nat.lor x y) (at level 50) : nat_scope.
Notation "x .- y" := (Nat.ldiff x y) (at level 50) : nat_scope.
Notation "x .^ y" := (Nat.lxor x y) (at level 50) : nat_scope.
Notation "x .[ i ]" := (Nat.testbit x i) : nat_scope.
Notation "a ^^ b" := (xorb a b) (at level 50) : nat_scope.

(**
## 整数のビット演算の定義
*)
Section a.

  Definition lnot (x : int) : int :=
    match x with
    | (Posz n) => Negz n
    | (Negz n) => Posz n
    end.
    
  Definition land (x y : int) : int :=
    match x, y with
    | (Posz m), (Posz n) => Posz (Nat.land m n)  (* x & y *)
    | (Posz m), (Negz n) => Posz (Nat.ldiff m n) (* x & ~y *)
    | (Negz m), (Posz n) => Posz (Nat.ldiff n m) (* ~x & y *)
    | (Negz m), (Negz n) => Negz (Nat.lor m n)   (* ~x & ~y = ~(x | y) *)
    end.
End a.

Notation ".~ x" := (lnot x) (at level 35) : int_scope.
Notation "x .& y" := (land x y) (at level 50) : int_scope.

(**
＃補題と帰納原理
*)

Section c.
(**
## 2を足していく帰納法（ひとつ飛びの帰納法）
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
## Coqのための補題
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
## 2で割っていく帰納法
 *)
  Lemma div2_lt : forall n, 2 <= n -> Nat.div2 n < n.
  Proof.
    case => [| [| n' IH]] //.
    rewrite -2!addn1 leq_add2r.
    apply/leP/Nat.div2_decr.
    lia.
  Qed.
  
  Lemma div2_ind :
    forall (P : nat -> Prop),
      P 0 ->
      P 1 ->
      (forall n, 1 < n -> P n./2 -> P n) ->
      forall n, P n.
  Proof.
    move=> P H0 H1 Hstep.
    Check (well_founded_induction lt_wf)
      : forall P : nat -> Set,
        (forall x : nat, (forall y : nat, (y < x)%coq_nat -> P y) -> P x) -> forall a : nat, P a.
    apply: (well_founded_induction lt_wf). (* lt について整礎帰納法を使う。 *)
    case=> [| [|]] //= n IH. (* n を 0 と 1 と n'+2 に場合分けする。 *)
    apply: Hstep => //.
    apply: IH.
    apply/ltP.
    rewrite -coq_divn2.
    by apply div2_lt.
  Qed.
  
(**
## 偶数+1 diff 偶数 = 1
 *)
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

(**
## 

pd 関数の引数が 0 以外の偶数の場合、testbit_div2 のようなことになる。
*)
  Check Nat.testbit_div2 : forall a n : nat, (Nat.div2 a).[n] = a.[n.+1].
  Lemma halfDiff (m n : nat) : (m .- n)./2 = m./2 .- n./2.
  Proof.
    have H x : x./2 = (x / 2 ^ 1)%coq_nat by rewrite Nat.pow_1_r -Nat.div2_div coq_divn2.
    rewrite 3!H.
    rewrite -3!Nat.shiftr_div_pow2.
    by rewrite Nat.shiftr_ldiff.
  Qed.
  
  Lemma mul2K n : n.*2./2 = n.
  Proof.
    lia.
  Qed.

(**
## testbit が全単射
*)
  Lemma testbit_inj m n : (forall i, m.[i] = n.[i]) -> m = n.
  Proof.
    move=> H.
    by apply: Nat.bits_inj.
  Qed.
End c.

(**
# 問題の形式化
 *)

(**
## 数学ガールの式
*)
Module mg.
Section mg.
  Open Scope int_scope.
  
  Definition p (x : int) : int := x .& (- x).

  Equations log2 (x : int) : nat :=
    log2 (Posz n) := Nat.log2 n;
    log2 (Negz _) := 0.
  Compute log2 0%Z.                         (* = 0%N *)
  
  Definition ruler (x : int) := log2 (p x).
End mg.
End mg.

Section b.
  (**
## 自然数化した式
*)  
  Definition p (n : nat) : nat := n .- n.-1.

  Definition ruler (n : nat) : nat := Nat.log2 (p n).
  
  (**
## ルーラー関数の漸化式
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
    by simp ruler_rec.    (* rewrite ruler_rec_clause_2_equation_1. *)
  Qed.

  Lemma ruler_rec_even (n : nat) : (0 < n)%N -> ~~ odd n -> ruler_rec n = (ruler_rec n./2).+1.
  Proof.
    case: n => //= n Hn.
    rewrite negbK => He.
    simp ruler_rec => //=.
    rewrite He.
    simp ruler_rec.    (* rewrite ruler_rec_clause_2_equation_2 /=. *)
    done.
  Qed.
  
(**
# いくつかの証明

以上で、

- 数学ガールのルーラー関数
- 自然数化したルーラー関数
- ルーラー関数の漸化式

の3つに定義が得られました。数学ガールの式と自然数化した式が等しいことの証明を済ませておきます。
*)
  Lemma mg_p__p (n : nat) : mg.p n = p n.
  Proof.
    by case: n.
  Qed.

  Lemma mg_ruler__ruler (n : nat) : mg.ruler n = ruler n.
  Proof.
    rewrite /mg.ruler /ruler.
    by rewrite mg_p__p.
  Qed.    

(**
以下で、自然数化したルーラー関数とルーラー関数が等しいことを証明すれば、
数学ガールのルーラー関数とルーラー関数の漸化式が等しいことが証明できます。
*)
End b.

(**
# p関数の性質
*)
Section d.
(**
## pd 関数の引数が奇数の場合、値は 1 である。
*)
  Lemma p_odd__1 (n : nat) (i : nat) : odd n -> p n = 1.
  Proof.
    case: n => //= n Hno.
    rewrite /p -pred_Sn.
    by rewrite ldiff_even_n_n1_diff_n__1 //.
  Qed.
  
(**
## p 関数の引数が偶数の場合、./2 した値から再帰的に求められる。testbit版
*)
  Lemma p_even_testbit (n i : nat) : (0 < n)%N -> ~~ odd n -> (p n).[i.+1] = (p n./2).[i].
  Proof.
    case: n => //= n _ Ho.
    rewrite /p.
    rewrite -pred_Sn.
    rewrite negbK in Ho.
    (* rewrite Nat.testbit_div2. *)
    rewrite coq_divn2 halfDiff uphalfE.
    congr ((_ .- _) .[ _]).
    lia.
  Qed.

  (* 似た補題 *)
  Lemma p_even'_testbit (n i : nat) : (0 < n)%N -> (p n.*2).[i.+1] = (p n).[i].
  Proof.
    move=> Hn0.
    rewrite (@p_even_testbit n.*2); try lia.
    by rewrite mul2K.
  Qed.
  
(**
## p 関数の引数が偶数の場合、./2 した値から再帰的に求められる。2倍版
*)

  (* p_even の証明では、doubleDiff 補題が使えそうだが、正しい証明にならない。
     なぜなら、= になるのは別な理由であるからだ。 *)
  (* その代わりに、testbit の単射性 testbit_inj を使う。 *)
  
  Check Nat.testbit_even_succ' : forall a i : nat, (2 * a)%coq_nat.[i.+1] = a.[i].
  
  Lemma p_even_nm2_0bit n : (p n.*2).[0] = false.
  Proof.
    rewrite /p Nat.ldiff_spec /=.
    rewrite -coq_muln2 Nat.odd_even.
    done.
  Qed.
  
  Lemma p_even_pm2_0bit n : (p n).*2.[0] = false.
  Proof.
    rewrite /p.
    rewrite -coq_muln2 Nat.testbit_even_0.
    done.
  Qed.
  
  Lemma p_even_d2pm2_0bit n : (p n./2).*2.[0] = false.
  Proof.
    rewrite /p.
    rewrite -coq_muln2 Nat.testbit_even_0.
    done.
  Qed.

  Lemma p_even_0bit n : ~~ odd n -> (p n).[0] = false.
  Proof.
    move=> He.
    rewrite -[n in (p n)]even_uphalfK //=.
    rewrite -Nat.bit0_odd.
    by rewrite p_even_nm2_0bit.
  Qed.
  
  (* 苦労した補題 *)
  Lemma p_even (n : nat) : (0 < n)%N -> ~~ odd n -> (p n) = (p n./2).*2.
  Proof.
    move=> Hn He.
    apply: testbit_inj => i.
    case: i => [| n']. (* i を 0 か 1以上で分ける。避けられないか？ *)
    - by rewrite p_even_d2pm2_0bit p_even_0bit.
    - rewrite -coq_muln2.
      rewrite Nat.testbit_even_succ'.
      by rewrite p_even_testbit.
  Qed.
End d.


(**
# ルーラー関数の性質
 *)
Section e.
  (**
### 補題
   *)
  (* 引数が1以上なら、値は1以上である。./2 による帰納法で求める。 *)
  Lemma p_gt_0 n : 0 < n -> 0 < p n.
  Proof.
    elim/div2_ind : n => //= n Hn1 IHn Hn.
    have := orbN (odd n).
    case/orP => Heo.
    (* n が奇数のとき、p n = 1 *)
    - by rewrite p_odd__1.
    (* n が偶数のとき、帰納法を使う。 *)
    - rewrite p_even //=.
      rewrite double_gt0.
      apply: IHn.
      lia.
  Qed.
  
  Lemma p_gt_0' n : 0 < n -> ~~ odd n -> 0 < p n./2.
  Proof.
    move=> Hn He.
    Check @p_gt_0 (n./2).
    rewrite (@p_gt_0 (n./2)) //=.
    lia.
  Qed.
  
  (**
### 引数が0の時、値は0である。
  *)
  Lemma ruler_0 : ruler 0 = 0.
  Proof.
    done.
  Qed.

  (**
### 引数が奇数のとき、値は0である。
   *)
  Lemma ruler_odd (n : nat) : odd n -> ruler n = 0.
  Proof.
    move=> Ho.
    by rewrite /ruler p_odd__1.
  Qed.
  
  (**
### 引数が偶数のとき、./2の値から再帰的に求めることができる。
   *)
  Lemma ruler_even (n : nat) : (0 < n)%N -> ~~ odd n -> ruler n = (ruler n./2).+1.
  Proof.
    move=> Hn He.
    rewrite /ruler.
    rewrite -Nat.log2_double.
    - f_equal.                              (* log2 を消す。 *)
      rewrite coq_muln2.
      by rewrite p_even.
    - apply/ltP.
      by rewrite p_gt_0'.
  Qed.

End e.

(**
##

任意の自然数 n について、ruler と ruler_rec が等しい。
*)
Section f.

  Lemma ruler_rec__ruler (n : nat) : ruler n = ruler_rec n.
  Proof.
    elim/div2_ind : n => [|| n H1 IH].
    - by rewrite ruler_0.                  (* 0 の場合 *)
    - by rewrite ruler_odd.                (* 1 の場合 *)
    - have := orbN (odd n).                 (* 偶奇で場合分けする。 *)
      case/orP => Heo.
      + case: n H1 IH Heo.                  (* 奇数の場合 *)
        * by rewrite ruler_0.              (* 0の場合 *)
        * move=> n H1 IH Ho.                (* 1以上の場合 *)
          rewrite ruler_odd //=.
          by rewrite ruler_rec_odd.
      + rewrite ruler_even; try lia.       (* 偶数の場合 *)
        rewrite ruler_rec_even; try lia.
  Qed.

End f.

(**
# 最後に

最後に、数学ガールのルーラー関数とルーラー関数の漸化式が等しいことの証明をします。
*)
Theorem mg_ruler__ruler_rec (n : nat) : mg.ruler n = ruler_rec n.
Proof.
  rewrite mg_ruler__ruler.
  rewrite ruler_rec__ruler.
  done.
Qed.

(**
# Appendix

ProofCafe mh氏による。
*)
Section g.
  Open Scope int_scope.
  
  Equations lor (x y : int) : int :=
    lor (Posz m) (Posz n) := Posz (Nat.lor m n);   (* x | y *)
    lor (Posz m) (Negz n) := Negz (Nat.ldiff n m); (* ~(~x & ~ y) *)
    lor (Negz m) (Posz n) := Negz (Nat.ldiff m n); (* ~(~ x & ~y) *)
    lor (Negz m) (Negz n) := Negz (Nat.land m n).  (* ~(~x & ~y) *)
  
  Equations ldiff (x y : int) : int :=
    ldiff (Posz m) (Posz n) := Posz (Nat.ldiff m n); (* x & ~ y *)
    ldiff (Posz m) (Negz n) := Posz (Nat.land m n); (* x & ~ ~y = x & y *)
    ldiff (Negz m) (Posz n) := Negz (Nat.lor m n);  (* ~x & ~ y = ~(x | y) *)
    ldiff (Negz m) (Negz n) := Posz (Nat.ldiff n m). (* ~x & ~ ~y = ~ x & y *)

  Equations lxor (x y : int) : int :=
    lxor (Posz m) (Posz n) := Posz (Nat.lxor m n); (* x ^ y *)
    lxor (Posz m) (Negz n) := Negz (Nat.lxor m n); (* ~(x ^ ~y) *)
    lxor (Negz m) (Posz n) := Negz (Nat.lxor m n); (* ~(~x ^ y) *)
    lxor (Negz m) (Negz n) := Posz (Nat.lxor m n). (* ~x ^ ~y *)
  
  Equations testbit (x : int) (m : nat) : bool :=
  testbit (Posz n) m := Nat.testbit n m ;
  testbit (Negz n) m := ~~ Nat.testbit n m.
  
  Notation ".~ x" := (lnot x) (at level 35) : int_scope.
  Notation "x .& y" := (land x y) (at level 50) : int_scope.
  Notation "x .| y" := (lor x y) (at level 50) : int_scope.
  Notation "x .^ y" := (lxor x y) (at level 50) : int_scope.
  Notation "x .[ i ]" := (testbit x i) : int_scope.
  Notation "a ^^ b" := (xorb a b) (at level 50) : int_scope.

  (**
## spec
   *)
  Lemma lnot_spec (x : int) (i : nat) : (.~ x).[i] = ~~ x.[i].
  Proof.
    case: x => n; simp lnot testbit => //=.
    by rewrite negbK.
   Qed.

  (* この証明から 2025/8/23 ProorCafe *)
  Lemma land_spec (x y : int) (i : nat) : (x .& y).[i] = x.[i] && y.[i].
  Proof.
    case: x; case: y => m n;
                        simp testbit land;
                        rewrite ?Nat.land_spec ?Nat.lor_spec ?Nat.ldiff_spec //=.
    - by rewrite andbC.
    - by rewrite negb_or.
  Qed.
  
  Lemma lor_spec (x y : int) (i : nat) : (x .| y).[i] = x.[i] || y.[i].
  Proof.
    case: x; case: y => m n;
                        simp testbit lor;
                        rewrite ?Nat.lor_spec ?Nat.land_spec ?Nat.ldiff_spec //=.
     - by rewrite negb_and negbK orbC.
     - by rewrite negb_and negbK orbC.
     - by rewrite negb_and.
   Qed.
  
  Lemma ldiff_spec (x y : int) (i : nat) : (ldiff x y).[i] = x.[i] && ~~ y.[i].
  Proof.
    case: x; case: y => m n;
                         simp testbit ldiff;
                         rewrite ?Nat.land_spec ?Nat.lor_spec ?Nat.ldiff_spec //=.
    - by rewrite negbK.
    - by rewrite negb_or.
    - by rewrite negbK andbC.
  Qed.
   
  Lemma lxor_spec (x y : int) (i : nat) : (x .^ y).[i] = xorb (x.[i]) (y.[i]).
  Proof.
    case: x; case: y => m n;
                        simp testbit lxor;
                        rewrite Nat.lxor_spec //=.
    - by rewrite Bool.negb_xorb_r.
    - by rewrite Bool.negb_xorb_l.
    - by rewrite -Bool.negb_xorb_l -Bool.negb_xorb_r negbK.
  Qed.
End g.

(**
# 注記

注1 小数点を導入して、有理数や実数の範囲に広げることもできますが、これは別の機会に。

注2 [1]の本文中にも、無限の桁数でも成り立つ、という言及はあります。
*)

(**
# 参考文献

[1] 結城浩「数学ガールの秘密ノート／ビットとバイナリ」SB Creative

[2] https://en.wikipedia.org/wiki/Ruler_function

[4] https://rocq-prover.github.io/platform-docs/equations/tutorial_basics.html
*)

(* END *)
