(**
「数学ガールの秘密ノート／ビットとバイナリ」のルーラー関数とその漸化式の証明
=========================
2025/08/10      @suharahiromichi

# はじめに

結城浩さんの「数学ガールの秘密ノート／ビットとバイナリ」[1]では、
ビット演算、すなわち、整数や自然数 (注1) を2進表現したときの桁どうしの演算を取り上げています。

ビット演算は、通常、2進4桁とか8桁とか32桁とかの有限の範囲で考えることが多く、[1]でも同様ですが (注2)
今回は、整数や自然数の範囲で考えてみたいと思います。

ご注意：この記事は[1]のネタバレ、および、演習問題の解答を含みます。
*)

(**
# 問題

(1) ``n & -n`` は何を意味するか。
ただし、``n``は1以上の自然数、``&``はビット毎の論理積、``-``は負号（2の補数）とする。

(2) ``log2 (n & -n)`` がルーラー関数 (Ruler function [2]) であることを示す。
ただし、``log2``は 2を底とする対数とする。

(3) ルーラー関数の漸化式を定義し、(2)と等しいことを証明する。


ルーラー関数というのは``n``を2進表現したときの「最も右側の``1``の桁数、
ただし0桁目から数える」を返す関数です。
値の進み方が定規の刻みに似ているのでこの名前がついたそうです。

例えば、n = 6 = 0110 なので、n=6のルーラー関数は1 となります。
ちょっと計算してみると、次のようになります。

| n | n     | -n     | n & -n | log2 (n & -n)  |
|:-:|:-----:|:------:|:------:|:--------------:|
| 1 | 00001 | 11111  | 00001  | 0  |
| 2 | 00010 | 11110  | 00010  | 1  |
| 3 | 00011 | 11101  | 00001  | 0  |
| 4 | 00100 | 11100  | 00100  | 2  |
| 5 | 00101 | 11011  | 00001  | 0  |
| 6 | 00110 | 11010  | 00010  | 1  |
| 7 | 00111 | 11001  | 00001  | 0  |
| 9 | 01000 | 11000  | 01000  | 3  |


``n & -n`` で 1 になるのはどれかひとつの桁で、``n - 1`` から ``n`` で
0から1に変化した最も右の桁にあたります。このことから、
n が奇数の場合は、``n & -n`` は 00001 になりルーラー関数に値は0になり、
n が偶数の場合は、``n/2`` のルーラー関数の値の ``+1`` になっていることがわかります。

非形式的な説明については、是非[1]を参照してください。
本記事では、(3)を形式化して証明する過程で、(1)や(2)を明らかにしていきます。
 *)

(**
# 証明の方針

オリジナルのルーラー関数の定義は、負数（2の補数）が含まれるところが面白いのですが、
扱う数の範囲が整数になり難しいので、それと同値の定義である

``log2 (n .- (n - 1))`` ただし ``.-`` は ldiff 関数


を使います。自然数の範囲で定義できるので「自然数化した式」と呼びます。

漸化式はもともと自然数の範囲で定義されているので、両者の同値の証明は簡単になります。

具体的な証明は log2 の中身（これを p 関数と呼びます）

``p(n) = n .- (n - 1)``


について、n が 奇数、偶数と場合分けして性質をしらべます。
これは、引数の ``1/2`` (div2) に関する帰納法を使い、
奇数のときに p 関数の値が 1 になることで、証明をするためです。

また、p 関数だけでは証明が進まないため、testbit関数を使用します。これは

``x.[i]``


x の i 桁目の値が 0 なら false、1 なら true を返すものです。

testbit関数は単射性があるため、すべての桁の値どうしが等しければ同じ値であることが言えます。

``(∀i, x.[i] = y.[i]) -> x = y``


この性質も有効に使います。
*)

(**
# 証明の道具立て

使い慣れているので MathComp を使いますが、MathComp ではビット演算が用意されていないので、
自然数のビット演算は、Standard Rocq のライブラリ (Arith) をインポートして使います。
MathComp の nat と Standard Rocq の Nat の自然数の定義は同じなので、概ね互換性があります。
わずかな非互換の箇所については説明します。

整数については、Standard Rocq の 整数 Z (ZArith) は使わず、MathComp の int の上で独自に定義します。
このとき Lean/Math4 [5] を参考にします。Lean の定義のほうが、MathComp に近いからです。

これとは別に、関数の定義には Rocq の Equations [3] を使用します。
*)

(**
ソースコードは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math4/ssr_ruler_qiita.v
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ssrZ zify ring lra.
(* opam install coq-equations *)
From Equations Require Import Equations.
Import Arith.                            (* Nat.Even, Nat.land_spec *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
なお、自然数の範囲では lnot 関数 ``.~ ○`` は定義されていない
（Rocq にも Lean にもない）ことに注意してください。
これは ``lnot 0 = ...11111`` となり計算が終了しないためです。
その代わりに、``● .& (.~ ○)`` にあたる ldiff 関数 ``● .- ○`` が用意されています。
これは、かならず計算が終了します。
*)

(**
## 整数のビット演算の定義
*)
Section a.

  Equations lnot (x : int) : int :=
    lnot (Posz n) := Negz n;
    lnot (Negz n) := Posz n.
  
  Equations land (x y : int) : int :=
    land (Posz m) (Posz n) := Posz (Nat.land m n);  (* x & y *)
    land (Posz m) (Negz n) := Posz (Nat.ldiff m n); (* x & ~y *)
    land (Negz m) (Posz n) := Posz (Nat.ldiff n m); (* ~x & y *)
    land (Negz m) (Negz n) := Negz (Nat.lor m n).   (* ~x & ~y = ~(x | y) *)
End a.

Notation ".~ x" := (lnot x) (at level 35) : int_scope.
Notation "x .& y" := (land x y) (at level 50) : int_scope.

(**
以上は Lean/Math4 [5] そのままです。
整数の場合は、``lnot 0 = -1`` となり、定義ができます。
*)

(**
# 問題の形式化
 *)

(**
## 数学ガールの式

[1] の定義をそのまま形式化すると、次のようになります。
``0 < x`` との制限がありますが、ここでは0を含めて定義し、
``log2 0 = 0`` として扱います。

負号（2の補数）が含まれることから、自然数ではなく整数の範囲での定義になります。
*)
Module mg.
Section mg.
  Open Scope int_scope.
  
  Definition p (x : int) : int := x .& (- x).

(**
整数を定義域にとるlog2を定義します。
値域は自然数として、0以下は0を返すようにします。
*)
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

本記事で実際に扱うのは、自然数の範囲で定義される次の式（以下 p 関数と呼びます）、
および、それの対数をとった ruler 関数です。
*)  
  Definition p (n : nat) : nat := n .- n.-1.

(**
``○ .- ○`` は ldiff 関数であり、``○ .& (.~ ○)`` です。すなわち、

```
n .- (n.-1) = n .& .~(n.-1) = n .& (- n)
```

です。ここで、2の補数は「全ビットを反転させてから +1 する」
から「-1 してから全ビットを反転する」を使っています。

```
- n = .~n + 1 = .~(n - 1)
```

この``- 1``は自然数の範囲で考えます。そのため、n は 1 以上となりますが、
ここでは、``n = 0`` の場合でも ``n .- (n - 1) = 0 .- 0 = 0`` とします。
*)

(**
log2 は自然数の範囲で Rocq ライブラリにあるものが使えます。
*)
  Definition ruler (n : nat) : nat := Nat.log2 (p n).
  
(**
## ルーラー関数の漸化式

前出のルーラー関数の定義にあわせて、
引数が0のとき値を0にしています。
停止性が判らないので、それを証明します。
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
# いくつかの証明

以上で、

- 数学ガールのルーラー関数
- 自然数化したルーラー関数
- ルーラー関数の漸化式


の3つの定義が得られました。
まず、数学ガールのオリジナルな式と、
自然数化した式が等しいことの証明を済ませておきます。
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
以下で、自然数化したルーラー関数と、ルーラー関数の漸化式が等しいことを証明すれば、
数学ガールのルーラー関数とルーラー関数の漸化式が等しいことが証明できることになります。
*)
End b.

(**
# 補題と帰納原理

最初にいくつかの補題と帰納原理を証明しておきます。
*)

Section c.
(**
## 2を足していく帰納法（ひとつ飛びの帰納法）

通常の1を足していく帰納法では解けない補題があるので、
ひとつ飛ばしの帰納原理を証明しておきます。
これは [4] で詳しく説明されているので、参考にしてください。
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

前述の通り、Standard Rocq の Nat と、MathComp の nat との自然数の定義は同じですが、
一部の述語や関数の定義に違いがあります。
それらを相互に変換する補題を証明しておきます。
いずれも nat_ind2 を使います。
*)

(**
2で割るdiv2 と、MathComp の half関数 (./2 演算子)の同値を証明します。
*)
  Lemma coq_divn2 n : Nat.div2 n = n./2.
  Proof.
    elim/nat_ind2 : n => //= n IHn.
    by rewrite IHn.
  Qed.
  
(**
偶奇判定の EvenとOdd述語と、MathComp の odd述語の同値を証明します。
*)
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
このほか、le (<=) や lt (<) の定義の同値を示す補題は用意されているので、使います。
*)  
  Check @leP : forall m n : nat, reflect (m <= n)%coq_nat (m <= n).
  Check @ltP : forall m n : nat, reflect (m < n)%coq_nat (m < n).

(**
頻出する2倍についての補題も証明しておきます。
*)
  Lemma coq_muln2 (n : nat) : (2 * n)%coq_nat = n.*2.
  Proof.
    lia.
  Qed.

(**
## 2で割っていく帰納法（div2 についての帰納法）

この記事では、2で割っていく帰納法が重要になります。
ルーラー関数の性質から、任意の自然数 n について、
それを 2 で割っていくことでいつかは奇数になり、ルーラー関数の値が0になるからです。

この定義と証明は ChatGPT の解答をもとに
well_founded_induction 補題を使いましたが、
ほかに証明の方法はあるかもしれません。
*)
  Lemma div2_lt : forall n, 1 < n -> Nat.div2 n < n.
  Proof.
    case=> [| [| n' IH]] //.
    rewrite -2!addn1 leq_add2r.
    apply/leP/Nat.div2_decr.
    lia.
  Qed.
  
  Lemma div2_ind : forall (P : nat -> Prop),
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
## ldiff についての補題

隣り合った奇数と偶数の ldiff は 1 になります。
これを証明します。
より一般的なかたちで証明されているので、それから導きます。
*)
  Lemma ldiff_odd_even__1 n : ~~ odd n -> n.+1 .- n = 1.
  Proof.
    move/even_halfK => <-.
    rewrite -muln2 mulnC -addn1.
    
    Check Nat.ldiff_odd_even n n
      : Nat.ldiff ((2 * n)%coq_nat + 1)%coq_nat (2 * n)%coq_nat
        = ((2 * Nat.ldiff n n)%coq_nat + 1)%coq_nat.
    
    rewrite Nat.ldiff_odd_even Nat.ldiff_diag.
    rewrite Nat.mul_0_r Nat.add_0_l.
    done.
  Qed.

(**
ldiff は、引数の``./2``について結果が保存されます。
*)
  Lemma halfDiff (m n : nat) : (m .- n)./2 = m./2 .- n./2.
  Proof.
    have H x : x./2 = (x / 2 ^ 1)%coq_nat
      by rewrite Nat.pow_1_r -Nat.div2_div coq_divn2.
    rewrite 3!H.
    rewrite -3!Nat.shiftr_div_pow2.
    by rewrite Nat.shiftr_ldiff.
  Qed.
  
(**
## testbit が全単射

2進数の任意の桁（任意のビット）が同じ値であるふたつの数は、等しいといえます。
これは強力なツールになるので、使用します。
これもより一般的なかたちで証明されているので、それから導きます。
*)
  Lemma testbit_inj m n : (forall i, m.[i] = n.[i]) -> m = n.
  Proof.
    move=> H.
    by apply: Nat.bits_inj.
  Qed.

(**
## ルーラー関数の漸化式 ruler_rec の定義から明らかな性質

ルーラー関数の漸化式 ruler_rec の定義から比較的簡単に導かれる性質を証明しておきます。
引数が 0、奇数、偶数のそれぞれの場合について示します。
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
    by simp ruler_rec.
  Qed.

  Lemma ruler_rec_even (n : nat) : (0 < n)%N -> ~~ odd n ->
                                   ruler_rec n = (ruler_rec n./2).+1.
  Proof.
    case: n => //= n Hn.
    rewrite negbK => He.
    simp ruler_rec => //=.
    rewrite He.
    by simp ruler_rec.
  Qed.
End c.

(**
# p 関数の性質
*)
Section d.
(**
## p 関数の引数が奇数の場合

値は 1 であることを直接求めます。
*)
  Lemma p_odd__1 (n : nat) (i : nat) : odd n -> p n = 1.
  Proof.
    case: n => //= n Hno.
    rewrite /p -pred_Sn.
    by rewrite ldiff_odd_even__1 //.
  Qed.
  
(**
## p 関数の引数が偶数の場合

0ビット目はかならず 0 です。
*)
  Lemma p_even_0bit n : ~~ odd n -> (p n).[0] = false.
  Proof.
    move=> He.
    rewrite -[n in (p n)]even_uphalfK //=.
    rewrite -Nat.bit0_odd.
    rewrite /p Nat.ldiff_spec /=.
    by rewrite -coq_muln2 Nat.odd_even.
  Qed.
  
(**
0ビット目以外は、1/2した値から再帰的に求められます。
*)
  Lemma p_even_testbit (n i : nat) : (0 < n)%N -> ~~ odd n -> (p n).[i.+1] = (p n./2).[i].
  Proof.
    case: n => //= n _ Ho.
    rewrite /p.
    rewrite -pred_Sn.
    rewrite negbK in Ho.
    rewrite coq_divn2 halfDiff uphalfE.
    congr ((_ .- _) .[ _]).
    lia.
  Qed.
  
(**
testbit の単射性をつかって、testbit を外しておきます。
*)
  Lemma p_even (n : nat) : (0 < n)%N -> ~~ odd n -> (p n) = (p n./2).*2.
  Proof.
    move=> Hn He.
    apply: testbit_inj => i.
    case: i => [| n'].
    - by rewrite -coq_muln2 Nat.testbit_even_0 p_even_0bit.
    - rewrite -coq_muln2.
      rewrite Nat.testbit_even_succ'.
      by rewrite p_even_testbit.
  Qed.
End d.

(**
## p 関数の値は 1以上

あとで必要となるので、p関数の引数が1以上なら、値は1以上であることを証明します。
これには、div2 による帰納法を使います。
*)
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
# ルーラー関数の性質

p 関数の性質から、ルーラーの性質をみていきます。
引数が 0、奇数、偶数のそれぞれの場合について示します。
前出のルーラー関数の漸化式の性質と同じ場合分けにしています。
 *)
Section e.
(**
## 引数による場合分け

引数が0の時、値は0です。
*)
  Lemma ruler_0 : ruler 0 = 0.
  Proof.
    done.
  Qed.

(**
引数が奇数のとき、値は0です。
*)
  Lemma ruler_odd (n : nat) : odd n -> ruler n = 0.
  Proof.
    move=> Ho.
    by rewrite /ruler p_odd__1.
  Qed.
  
(**
引数が偶数のとき、./2の値から再帰的に求めることができます。
*)
  Lemma ruler_even (n : nat) : (0 < n)%N -> ~~ odd n -> ruler n = (ruler n./2).+1.
  Proof.
    move=> Hn He.
    rewrite /ruler.
    rewrite -Nat.log2_double.
    - congr (Nat.log2 _).                   (* log2 を消す。 *)
      rewrite coq_muln2.
      by rewrite p_even.
    - apply/ltP.
      by rewrite p_gt_0'.
  Qed.
End e.

(**
## 自然数化したルーラー関数とルーラー関数の漸化式が等しい

上記で示した性質を使って、任意の自然数 n について、ruler と ruler_rec が等しいことを示します。
偶数の場合帰納法が必要になるので、div2 についての帰納法を使用します。
*)
Section f.

  Lemma ruler__ruler_rec (n : nat) : ruler n = ruler_rec n.
  Proof.
    elim/div2_ind : n => [|| n H1 IH].
    - by rewrite ruler_0.                   (* 0 の場合 *)
    - by rewrite ruler_odd.                 (* 1 の場合 *)
    - have := orbN (odd n).                 (* 偶奇で場合分けする。 *)
      case/orP => Heo.
      + case: n H1 IH Heo.                  (* 奇数の場合 *)
        * by rewrite ruler_0.               (* 0の場合 *)
        * move=> n H1 IH Ho.                (* 1以上の場合 *)
          rewrite ruler_odd //=.
          by rewrite ruler_rec_odd.
      + rewrite ruler_even; try lia.        (* 偶数の場合 *)
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
  rewrite ruler__ruler_rec.
  done.
Qed.

(**
# Appendix

本記事で使用しなかった整数のビット演算についての定義と補題の証明を記載しておきます。
これは、ProofCafe mh氏によります。
*)
Section g.
  Open Scope int_scope.
  
(**
## ビット演算の定義
*)
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
  
  Notation "x .| y" := (lor x y) (at level 50) : int_scope.
  Notation "x .^ y" := (lxor x y) (at level 50) : int_scope.
  Notation "x .[ i ]" := (testbit x i) : int_scope.
  Notation "a ^^ b" := (xorb a b) (at level 50) : int_scope.

(**
## 補題

上記のビット演算が正しいことを示すために、整数版のtestbitを使って、
ビット演算をboolの論理演算に変換できることを証明します。
*)
  Lemma lnot_spec (x : int) (i : nat) : (.~ x).[i] = ~~ x.[i].
  Proof.
    case: x => n; simp lnot testbit => //=.
    by rewrite negbK.
   Qed.

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

[1] 結城浩「数学ガールの秘密ノート／ビットとバイナリ」SBクリエィティブ

[2] https://en.wikipedia.org/wiki/Ruler_function

[3] https://rocq-prover.github.io/platform-docs/equations/tutorial_basics.html

[4] https://softwarefoundations.cis.upenn.edu/lf-current/IndPrinciples.html

[5] https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Int/Bitwise.lean
*)

(* END *)
