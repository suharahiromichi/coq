(**
ユーグリッド除法 Euclidean division
========================

@suharahiromichi

2020/08/25
 *)

(**
# はじめに

小学校で習う整数の剰余付き割算は、整除法、または、ユーグリッド除法と呼ばれ、
整数 m, d, q, r に対して、与えられた m, q から d, r を求めることと定式化されます。


```math
\begin{eqnarray}
d &\ne& 0               \tag{1.1} \\

m &=& q d + r           \tag{1.2} \\

| r | &\lt& | d |       \tag{1.3} \\
\end{eqnarray}

```

ここで、m を被除数、d を除数、q を商、r を剰余または余り、と呼ぶ場合もあります。

しかし、式(1.3)から分かるとおり、この定式化では d, rは一意に決まりません。

具体的にいうと、$ 10 \div 3 $ の結果が 3 余り 1 でも、4 余り -2 であっても
式を満たすからです。
このことが、プログラミング言語の C と Python と Pascal とで、
剰余計算の結果が異なることの理由です。

一意性を担保するには、剰余の範囲をより狭く制限する必要があります。
たとえば、教科書に記載されるのは、

$$ 0 \le r \lt | d | \tag{1.3'} $$

にように、剰余を正の範囲に制限することです。
これは、プログラミング言語Pascalの ``mod`` 演算で採用されています。
また Coq/MathComp の ``%%`` もこの定義です。

これを満たす d と r を求めるには、次のふたつの方法があります。

- ``m / d`` を実数で求め、切り捨てて、qとする。
- ``|m| / |d|`` と絶対値で求め、mが正なら切り捨て、mが負なら切り上げ(注1)し、


符号を復元して(注2)、qとする。

(注1) 自然数の割算における切り捨てと切り上げは後で定義します。

(注2) m と d と q の符号は、奇数個の関係にあります。


ここでは、後者の絶対値の除算を使う方法を採用します。そして、

- r が 0 以上の制限を加えると、qとrが一意に決まることを証明する。
- q と r を求める式を具体的に定義して、式(1.2)と式(1.3')が成り立つことを証明する。

これによって、整数割算が持つ意味の健全性を示すことができるはずです。
証明には Coq/MathComp を使います。
MathCompにも``intdiv.v``で整数割算が定義されていますが、ここでは独自に実装してみます。

最後に、ここで示した以外の整除法について言及します。

このファイルは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_ediv.v

証明スクリプトは模範回答ではなく、一例として参考程度にしてください。
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import ssromega.                    (* ssromega タクティク *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)

(**
# 整数について

## 概説
 *)
(**
### 整数演算と自然数演算の変換（%:Zの分配則）

整数の文脈の中で、自然数を書くとコアーションで正整数になる（Posz これは _%:Z と同じ）。

_%Nで自然数のスコープを明示することができるが、この外に出た時点で、
同様にコアーションで正整数になる。すなわち、``_%:Z`` は分配できるわけである。

addやsubやleやltやdivやmodの演算は、整数と自然数でまったく別の定義であることに注意すること。
 *)

Section INT.
  Variable m n d : nat.
  
  (* 左辺は自然数の加算、右辺は整数の加算であり、ディフォルトの環（整数）で比較している。 *)
  Check PoszD m n : ((m + n)%N%:Z = m%:Z + n%:Z)%Z. (* m + n = (m + n)%N と見える。 *)
  Check PoszM m n : ((m * n)%N%:Z = m%:Z * n%:Z)%Z. (* (m * n)%N = m * n *)

  Check subzn : forall m n : nat, (n <= m)%N -> (m%:Z - n%:Z = (m - n)%N)%Z.
  Check lez_nat m n : ((m%:Z <= n%:Z) = (m <= n)%N)%Z.
  Check ltz_nat m n : ((m%:Z < n%:Z) = (m < n)%N)%Z.
  Check divz_nat n d : ((n %/ d)%Z = (n %/ d)%N)%Z.
  Check modz_nat m d : ((m %% d)%Z = (m %% d)%N)%Z.
End INT.

(**
####
*)
Lemma oppz_add' (x y : int) : (- (x + y) = -x + -y)%R.
Proof.
  Check oppz_add x y : (- (x + y) = -x + -y)%R.
    by apply: oppz_add.
Qed.

(**
## 補題

MathCompで整数に扱いになれていないひとのために（大抵のひとはそうでしょう）
再利用性のありそうなスクリプトを補題としてまとめておきます。
*)

(**
### ありがちな補題
 *)

(* 符号を移項するだけの補題 *)
Lemma opptr (x y : int) : x = - y -> - x = y.
Proof.
  move=> ->.
    by rewrite opprK.
Qed.

(* 絶対値を付けるだけの補題 *)
Lemma eq_eqabsabs (x y : int) : x = y -> `|x| = `|y|.
Proof. by move=> ->. Qed.

(* いつも欲しくなる補題の整数版 *)
Lemma lt_le (x y : int) : x < y -> x <= y.
Proof.
  move=> H.
  rewrite ler_eqVlt.
    by apply/orP/or_intror.
Qed.

Lemma nge_lt (m n : int) : (m <= n) = false -> n < m.
Proof.
  move/negbT.
    by rewrite -ltrNge.
Qed.

Lemma eq_subn (n : nat) : (n - n = 0)%N.    (* 自然数の補題 *)
Proof. apply/eqP. by rewrite subn_eq0. Qed.

Lemma eq_subz (x : int) : x - x = 0.        (* 整数の補題 *)
Proof. by rewrite addrC addNr. Qed.

(**
### 絶対値を操作する補題
 *)
Section ABS.
  Variable m : nat.
  Variable x : int.
  
(**
自然数の文脈と整数の文脈とで、関数が異なる（当然だが）。
 *)
  Check absz : int -> nat.                  (* |x|%N *)
  Check Num.Def.normr : int -> int.         (* |x|%Z *)

(**
両者の結果は、自然数から正整数へのコアーションで等しい。
*)  
  Check abszE x : `|x|%N%:Z = `|x|%Z.       (* `|x|%N = `|x| *)
  
(**
absz
*)  
  (* 自然数 *)
  Check absz_nat m : `| m%:Z |%N = m.       (* `|m|%N = m *)
  (* 正整数 *)
  Check gez0_abs : forall x : int, 0 <= x -> `|x|%N = x :> int. (* `|x|%N = x *)
  Check gtz0_abs : forall x : int, 0 < x -> `|x|%N = x :> int.
  (* 負整数 *)
  Check lez0_abs : forall x : int, x <= 0 -> `|x|%N = - x :> int.  
  Check ltz0_abs : forall x : int, x < 0 -> `|x|%N = - x :> int.  

(**
norm
*)
  (* 自然数 *)
  Lemma norm_nat (n : nat) : `| n%:Z | = n%:Z. (* `|n| = n *)
  Proof. by rewrite -abszE absz_nat. Qed.
  (* 正整数 *)
  Check @ger0_norm int_numDomainType x : 0 <= x -> `|x| = x :> int. (* `|x| = x *)
  Check @gtr0_norm int_numDomainType x : 0 < x -> `|x| = x :> int.
  (* 負整数 *)
  Check @ler0_norm int_numDomainType x : x <= 0 -> `|x| = - x :> int.
  Check @ltr0_norm int_numDomainType x : x < 0 -> `|x| = - x :> int.
End ABS.

Lemma abseq0_eq (x y : int) : (`|x - y| = 0)%N  <-> x = y.
Proof.
  split=> H.
  Check absz_eq0 : forall m : int, (`|m|%N == 0%N) = (m == 0).
  Check subr_eq0 : forall (V : zmodType) (x y : V), (x - y == 0) = (x == y).
  - move/eqP in H.
    rewrite absz_eq0 subr_eq0 in H.
      by apply/eqP.
  - apply/eqP.
    rewrite absz_eq0 subr_eq0.
      by apply/eqP.
Qed.

Lemma normq0_eq (x y : int) : `|x - y| = 0  <-> x = y. (* notu *)
Proof.
  split=> H.
  Check @normr0P : forall (R : numDomainType) (x : R), reflect (`|x| = 0) (x == 0).
  - move/normr0P in H.
    rewrite subr_eq0 in H.
      by apply/eqP.
  - apply/normr0P.
    rewrite subr_eq0.
      by apply/eqP.
Qed.

(**
# ユーグリッド除法の定義
*)
(**
## 準備

### 自然数の除算

最初に、自然数の除算を定義します。

切り捨て(floor)と切り上げ(ceil)の二種類です。

切り捨ては、自然数で定義された除算 (divn) とおなじです。

```math
\lfloor m / d \rfloor = divn(m, d)

```a

切り上げは、divn の結果に``+1``します。ただし、mがdで割り切れる場合はそのまま、
mがdで割りきれない場合は``+1``します。

```math
\lceil m / d \rceil =
\left\{
\begin{array}{ll}
divn(m, d) & (d | m) \\
divn(m, d) + 1 & (d \not| m)
\end{array}
\right.
```

 *)
Definition edivn_floor (m d : nat) : nat := (m %/ d)%N.

Definition edivn_ceil (m d : nat) : nat :=
  if (d %| m)%N then (m %/ d)%N else ((m %/ d).+1)%N.

(**
検算してみます。
*)
Compute edivn_floor  9 3.                   (* 3 *)
Compute edivn_floor 10 3.                   (* 3 *)
Compute edivn_ceil  9 3.                    (* 3 *)
Compute edivn_ceil 10 3.                    (* 4 *)

(**
### 自然数の除算の補題

自然数の除算の結果（商）に除数を掛けると、

- 切り捨ての場合は被除数以下
- 切り上げの場合は被除数以上

になります。
切り上げにおいて、等号が成立するのはmがdで割り切れる場合で、
そうでない場合は被除数未満となります。ふたつの条件をあわせて補題にしています。

```math
\lfloor m / d \rfloor d \le m \\
\lceil m / d \rceil d \ge m
```

これを補題として証明しておきます。
*)
Lemma edivn_floorp (m d : nat) : (edivn_floor m d * d <= m)%N.
Proof.
  rewrite /edivn_floor.
    by apply: leq_trunc_div.
Qed.

Lemma edivn_ceilp (m d : nat) : (d != 0)%N -> (m <= edivn_ceil m d * d)%N.
Proof.
  move=> Hd.
  rewrite /edivn_ceil.
  rewrite leq_eqVlt eq_sym.
  case: ifP => Hmd.
  (* m が d で、割りきれる場合 *)
  - apply/orP/or_introl.
      by rewrite -dvdn_eq.
  (* m が d で、割りきれない場合 *)
  - apply/orP/or_intror.
    rewrite ltn_ceil //.
      by rewrite lt0n.
Qed.

(* 証明できるもの *)
Lemma edivn_floor_lt_d' (m d : nat) : (0 < d)%N ->
                                      (m - edivn_floor m d * d)%:Z < d.
Proof.
  move=> Hd.
  rewrite /edivn_floor.
  (* rewrite ltz_nat. *)
  Search _ (_ %/ _ * _)%N.
  Check divn_eq m d.
  rewrite {1}(divn_eq m d).
  (* (m %/ d * d + m %% d - m %/ d * d)%N < d *)

  have -> (m' n' : nat) : (m' + n' - m' = n')%N by ssromega.
  (* rewrite subnn add0n. *)
  by apply: ltn_pmod.
Qed.

Check divn_eq : forall m d : nat, m = (m %/ d * d + m %% d)%N.

(*
Lemma test m d : (m %/ d)%N%:Z * d = (m %/ d * d)%N%:Z.
Proof.
  apply: subr0_eq.
    by rewrite eq_subz.
Qed.
*)

(* divn_eq' の整数加算版を用意する。内容は自然数の divn と modn である。 *)
Lemma divn_eq' (m d : nat) : m = (m %/ d * d)%N%:Z + (m %% d)%N :> int.
Proof.
  rewrite /divn modn_def.
  case: edivnP => q r //= Heq Hd.
  rewrite Heq.
  (* Goal : (q * d + r)%N = (q * d)%N + r *)
  done.
Qed.


(* 証明したいもの *)
Lemma edivn_floor_lt_d (m d : nat) : (0 < d)%N ->
                                     m%:Z - (edivn_floor m d * d)%:Z < d.
Proof.
  move=> Hd.
  rewrite /edivn_floor.
  Check divn_eq' m d.
  rewrite {1}(divn_eq' m d).
  (* (m %/ d * d)%N + (m %% d)%N - (m %/ d * d)%N < d *)
  rewrite -addrAC eq_subz add0r.
  Check ltn_pmod : forall m d : nat, (0 < d)%N -> (m %% d < d)%N.
    by apply: ltn_pmod.
Qed.

Lemma l_distr (d m : nat) : (m %/ d + 1)%N%:Z * d = (m %/ d * d)%N%:Z + d.
Proof.
  apply/eqP.
  rewrite eqz_nat.
  rewrite mulnDl.
  rewrite mul1n.
  done.
Qed.

Lemma edivn_ceil_lt_d (m d : nat) : (0 < d)%N ->
                                    (edivn_ceil m d)%:Z * d - m%:Z < d.
Proof.
  move=> Hd.
  rewrite /edivn_ceil.
  rewrite {1}(divn_eq' m d).
  case: ifP => H.
  (* 割り切れるので、m %% d = 0 の場合 *)
  - move/eqP in H.
    rewrite H /=.
    rewrite addr0.
    (* (m %/ d)%N * d - (m %/ d * d)%N < d *)
      by rewrite eq_subz.
      
  - rewrite opprD.
    rewrite addrCA addrA.
    rewrite -addn1.
    (* - (m %/ d * d)%N + (m %/ d + 1)%N * d - (m %% d)%N < d *)
    rewrite l_distr //=.
    rewrite addrA.
    Check (- (m %/ d * d)%N%:Z) + (m %/ d * d)%N%:Z + d - (m %% d)%N%:Z .
    rewrite [(- (m %/ d * d)%N%:Z) + ((m %/ d * d)%N%:Z)]addrC.
    rewrite eq_subz add0r.
    Search _ (_ - _ < _).
    rewrite ltr_subl_addl.
    Search _ (_ < _ + _).
    Check ltr_addr.
    rewrite ltr_addr.
    rewrite /dvdn in H.
    rewrite ltz_nat.
    rewrite -eqz_nat in H.
    move/negbT in H.
    Search _ (0 < _)%N.
    rewrite lt0n.
    apply/eqP => Hn.
    move/eqP in H.
    apply: H.
    f_equal.
    rewrite Hn.
    done.
Qed.

(**
## ユーグリッド除数の定義

直感的に説明するのが難しいので、数直線でも書いて納得してほしいのですが、
剰余を正とするためには、

- 被除数が正なら絶対値の割算で切り捨てしたあと除数の符号を反映します。
- 被除数が負なら絶対値の割算で切り上げしたあと除数の符号を反映し、さらに符号を反転します。

```math
m / d =
\left\{
\begin{array}{ll}
(sgn d) \lfloor |m| / |d| \rfloor & (m \ge 0) \\
- (sgn d) \lceil |m| / |d| \rceil & (m \lt 0) \\
\end{array}
\right.
```

ここで、sgn は符号関数です。

剰余は、被除数から商と除数の積を引いて求めます。これは整数で計算します。

```math
m\ rem\ d = m - (m / d) d
```
 *)
Definition edivz (m d : int) : int :=
  if (0 <= m) then
    sgz d * (edivn_floor `|m| `|d|)
  else
    - (sgz d * (edivn_ceil `|m| `|d|)).

Definition emodz (m d : int) : int := m - (edivz m d) * d.

(**
検算してみます。あっているようですね。
*)
Compute edivz 10 3.                         (* 3 *)
Compute edivz 10 (- 3%:Z).                  (* -3 *)
Compute edivz (- 10%:Z) 3.                  (* -4 *)
Compute edivz (- 10%:Z) (- 3%:Z).           (* 4 *)

Compute emodz 10 3.                         (* 1 *)
Compute emodz 10 (- 3%:Z).                  (* 1 *)
Compute emodz (- 10%:Z) 3.                  (* 2 *)
Compute emodz (- 10%:Z) (- 3%:Z).           (* 2 *)

(**
定義から自明ですが式(1.2)も成り立っています。
*)
Lemma edivz_eq (m d : int) : m = (edivz m d)%Z * d + (emodz m d)%Z.
Proof.
    by rewrite addrC subrK.
Qed.

(**
# 剰余が正であることの証明

先に、比較的やさしい剰余が正であることの証明をします。
証明するべきは以下です。

```math
m\ rem\ d \ge 0
```
*)

(**
## 定理 - 剰余は正
 *)
(**
証明はmの正負、すなわち、自然数の除算の切り捨てか切り上げで場合分けしたのち、
自然数の除算の補題を適用するだけの単純なものです。
*)
Lemma ediv_mod_ge0 (m d : int) : d != 0 -> 0 <= emodz m d.
Proof.
  move=> Hd.
  rewrite /emodz /edivz.
  case: ifP => H.
  - rewrite -mulrAC.
    rewrite -abszEsg mulrC.
    rewrite subr_ge0.
    move/normr_idP in H.
    rewrite -{2}H.
      by apply: edivn_floorp.

  - rewrite mulNr.
    (* m - - X は m + (- - X) なので、二重の負号 oppz を消します。 *)
    rewrite [- - (sgz d * edivn_ceil `|m| `|d| * d)]oppzK.
    rewrite -mulrAC.
    rewrite -abszEsg mulrC.
    move/nge_lt in H.
    Check opptr (ltr0_norm H).
    rewrite -{1}(opptr (ltr0_norm H)).
    rewrite addrC subr_ge0.
    apply: edivn_ceilp.
      by rewrite -lt0n absz_gt0.
Qed.

(**
## 定理 - 剰余は除数より小

 *)

Lemma ediv_mod_ltd (m d : int) : d != 0 -> emodz m d < `|d|.
Proof.
  move=> Hd.
  rewrite /emodz /edivz.
  case: ifP => Hm; case H : (0 <= d).
  
  (* m - sgz d * edivn_floor `|m| `|d| * d < `|d| *)
  - rewrite mulrAC.
    rewrite -abszEsg.
    rewrite mulrC.
    rewrite -{1}(gez0_abs Hm).
    Search _ ((_ - _ <  _)%N).
    Check edivn_floor_lt_d.
    apply: edivn_floor_lt_d.
      by rewrite -normr_gt0 in Hd.
    
  (*  m - sgz d * edivn_floor `|m| `|d| * d < `|d| *)    
  - rewrite mulrAC.
    rewrite -abszEsg.
    rewrite mulrC.
    rewrite -{1}(gez0_abs Hm).
    apply: edivn_floor_lt_d.
      by rewrite -normr_gt0 in Hd.
    
  (* m - - (sgz d * edivn_ceil `|m| `|d|) * d < `|d| *)    
  - rewrite mulNr mulrAC -abszEsg mulrC.
    move/nge_lt in Hm.
    rewrite opprK.
    rewrite -{1}(opptr (ltz0_abs Hm)).
    rewrite addrC.
    apply: edivn_ceil_lt_d.
      by rewrite -normr_gt0 in Hd.
    
  (* m - - (sgz d * edivn_ceil `|m| `|d|) * d < `|d| *)
  - rewrite mulNr mulrAC -abszEsg mulrC.
    move/nge_lt in Hm.
    rewrite opprK.
    rewrite -{1}(opptr (ltz0_abs Hm)).
    rewrite addrC.
    apply: edivn_ceil_lt_d.
      by rewrite -normr_gt0 in Hd.
Qed.

(**
まとめると、式(1.3')が成り立ちます。
*)
Lemma ediv_mod_ge0_ltd (m d : int) : d != 0 -> 0 <= emodz m d < `|d|.
Proof.
  move=> hd.
  apply/andP; split.
  - by apply: ediv_mod_ge0.
  - by apply: ediv_mod_ltd.
Qed.


(**
# 一意性の証明

式(1.1)から式(1.3)を満たす商qと剰余rがふたつあったとして、それが等しいことを証明します。
すなわち、

```math
\left\{
\begin{array}{ll}
m = q_{1} d + r_{1} \\
m = q_{2} d + r_{2} \\
\end{array}
\right
```

のとき、

```math
\left\{
\begin{array}{ll}
q_{1} = q_{2} \\
r_{1} = r_{2} \\
\end{array}
\right
```

であることを証明します。先に $ q_{1} = q_{2} $ を証明し、
ついで、$ r_{1} = r_{2} $ を証明します。
*)

Lemma lemma1 (q d : nat) : (q * d < d)%N -> (q = 0)%N.
Proof.
  rewrite -{2}[d]mul1n.
  Check ltn_mul2r
    : forall m n1 n2 : nat, (n1 * m < n2 * m)%N = (0 < m)%N && (n1 < n2)%N.
  rewrite ltn_mul2r.
  move/andP => [Hd Hq].
    by ssromega.
Qed.

Lemma lemma3 (q1 q2 r1 r2 d : int) :
  q1 * d + r1 = q2 * d + r2 -> (`|((q1 - q2) * d)%R|)%N = `|r1 - r2|%N.
Proof.
  move/eqP.
  Check subr_eq : forall (V : zmodType) (x y z : V), (x - z == y) = (x == y + z).
  rewrite -subr_eq.
  rewrite -addrA addrC eq_sym.
  rewrite -subr_eq.
  move/eqP/eq_eqabsabs.
  Check distrC.
  rewrite distrC.
  rewrite -mulrBl.
  (* ゴールの省略された型アノテーションを追加する。 *)
  Check `|((q1 - q2)%R * d)%R|%R = `|r1 - r2|%R ->
  `|((q1 - q2)%R * d)%R|%N = `|r1 - r2|%N.
  Check abszE : forall m : int, `|m|%N = `|m| :> int.

  move=> H.
  move/eqP in H.
  apply/eqP.
  (* Goal : `|((q1 - q2) * d)%R|%N == `|r1 - r2|%N *)
  rewrite -eqz_nat.                         (* ***** *)
  (* Goal :  `|(q1 - q2) * d| == `|r1 - r2| :> int *)
  done.
Qed.

Lemma lemma2 (r1 r2 : int) (d : nat) :
  0 <= r1 < d -> 0 <= r2 < d -> `|r1 - r2| < d.
Proof.
  move=> Hr1 Hr2.
  move/andP : Hr1 => [Hr1 Hr1d].
  move/andP : Hr2 => [Hr2 Hr2d].

  Search (_ < _ + _).
  Check ltr_paddr Hr2 Hr2d.
  move: (ltr_paddr Hr1 Hr1d) => Hr1dr1.
  move: (ltr_paddr Hr2 Hr1d) => Hr1dr2.
  move: (ltr_paddr Hr1 Hr2d) => Hr2dr1.
  move: (ltr_paddr Hr2 Hr2d) => Hr2dr2.
  Check ger0_norm Hr1.
  rewrite -(ger0_norm Hr1) in Hr1d.
  rewrite -(ger0_norm Hr2) in Hr2d.
  rewrite -(ger0_norm Hr1) in Hr1dr1.
  rewrite -(ger0_norm Hr1) in Hr1dr2.
  rewrite -(ger0_norm Hr1) in Hr2dr1.
  rewrite -(ger0_norm Hr2) in Hr1dr2.
  rewrite -(ger0_norm Hr2) in Hr2dr1.
  rewrite -(ger0_norm Hr2) in Hr2dr2.

  case H : (r1 - r2 >= 0).
  - move: {+}H => H'.
    rewrite -(ger0_norm Hr1) in H'.
    rewrite -(ger0_norm Hr2) in H'.    
    have H'' : `|r2| <= `|r1| by rewrite -subr_ge0.
    
    move/normr_idP in H.
    rewrite H.
    rewrite -(ger0_norm Hr1).
    rewrite -(ger0_norm Hr2).
    
    Check ltn_sub2r : forall p m n : nat, (p < n)%N -> (m < n)%N -> (m - p < n - p)%N.
    Check @ltn_sub2r `|r2| `|r1| (d + `|r2|) Hr2dr2 Hr1dr2
                                 : (`|r1| - `|r2| < d + `|r2| - `|r2|)%N.
    have H2 := @ltn_sub2r `|r2| `|r1| (d + `|r2|) Hr2dr2 Hr1dr2.
    (* H2 : (`|r1| - `|r2| < d + `|r2| - `|r2|)%N ここでnatになる。 *)
    
    rewrite -addnBA in H2 ; last done.
    rewrite (eq_subn `|r2|) in H2.
    rewrite addn0 in H2.
    (* ***** *)
    rewrite -ltz_nat in H2.
      by rewrite -subzn in H2.
      
  - move: {+}H => H'.
    rewrite -(ger0_norm Hr1) in H'.
    rewrite -(ger0_norm Hr2) in H'.    
    have H'' : `|r1| <= `|r2|.
    + move/nge_lt in H'.
      Search _ (_ - _ < 0).
      rewrite subr_lt0 in H'.
      rewrite ler_eqVlt.
        by apply/orP/or_intror.
        
    + move/negbT in H.
      rewrite -ltrNge in H.

      move/lt_le in H.
      rewrite ler0_def in H.
      move/eqP in H.
      rewrite H.
      Search _ (- ( _ - _ )).
      rewrite opprB.

      rewrite -(ger0_norm Hr1).
      rewrite -(ger0_norm Hr2).
      Check @ltn_sub2r `|r1| `|r2| (d + `|r1|) Hr1dr1.
      have H1 := @ltn_sub2r `|r1| `|r2| (d + `|r1|) Hr1dr1 Hr2dr1.
      rewrite -addnBA in H1 ; last done.
      rewrite (eq_subn `|r1|) in H1.
      rewrite addn0 in H1.
      (* ***** *)
      rewrite -ltz_nat in H1.
      rewrite -subzn in H1.
      * done.
      * done.
Qed.

Lemma edivz_uniqness_q (r1 r2 q1 q2 m d : int) :
  0 <= r1 < `|d| ->
                 0 <= r2 < `|d| ->
                                m = q1 * d + r1 ->
                                m = q2 * d + r2 ->
                                q1 = q2.
Proof.
  move=> Hr1 Hr2 Hq1 Hq2.
  apply/abseq0_eq.
  Check @lemma1 `|q1 - q2| `|d|.
  apply: (@lemma1 `|q1 - q2| `|d|).
  Check abszM.
  rewrite -abszM.
  rewrite Hq1 in Hq2.
(*  
  move/andP : Hr1 => [Hr1 Hr1d].
  move/andP : Hr2 => [Hr2 Hr2d].
*)
  Check @lemma3 q1 q2 r1 r2 d.
  Check @lemma3 q1 q2 r1 r2 d Hq2.
  rewrite (@lemma3 q1 q2 r1 r2 d Hq2).

  apply: lemma2.
  - done.
  - done.
Qed.

Lemma edivz_uniqness_r (r1 r2 q m d : int) :
  m = q * d + r1 ->
  m = q * d + r2 ->
  r1 = r2.
Proof.
  move=> Hq1 Hq2.  
  rewrite Hq1 in Hq2.
  rewrite [RHS]addrC in Hq2.
  rewrite [LHS]addrC in Hq2.
  move/eqP in Hq2.
  rewrite -subr_eq in Hq2.
  move/eqP in Hq2.
  rewrite -[LHS]addrA in Hq2.
  rewrite eq_subz in Hq2.
  rewrite addr0 in Hq2.
  done.
Qed.

(**
# 整除法のまとめ
*)

(**
式(1.3)の絶対値の記号を外すと、つぎの式を得る。


```math
\begin{eqnarray}
0 &\le& r \lt d         \tag{2.1} \\

0 &\le& -r \lt d        \tag{2.2} \\

d &\lt& -r \le 0        \tag{2.3} \\

d &\lt& r \le 0         \tag{2.4} \\

\end{eqnarray}

```

d は与えられるので、それを踏まえて、(2.1)〜(2.4)の式を選ぶことになる。
*)

(**
## 剰余が正（Pascal の ``mod``演算子）

```math
\begin{eqnarray}
0 \le r \lt d, ただし d \ge 0 \\
d \lt -r \le 0, ただし d \lt 0 \\`
\end{eqnarray}

```

このふたつに式は、$|d|$を使ってひとつにまとめられる。

$$ 0 \le r \lt | d | $$

| m  |  d | q  | r  | 実数除算 | 絶対値除算 | 例    |商  | 余  |
|:--:|:--:|:--:|:--:|:-------:|:----------:|:-----:|:--:|:---:|
| 正 | 正 | 正 | 正 | floor   | floor      |  10÷3  | 3 |  1  |
| 正 | 負 | 負 | 正 | ceil    | floor      | 10÷-3  |-3 |  1  |
| 負 | 正 | 負 | 正 | floor   | ceil       | -10÷3  |-4 |  2  |
| 負 | 負 | 正 | 正 | ceil    | ceil       | -10÷-3 | 4 |  2  |
 *)

(**
## 剰余が被除数と同符号（C の ``%``演算子）

```math
\begin{eqnarray}
0 \le r \lt d, ただし m \ge 0 \\
d \lt -r \le 0, ただし m \lt 0 \\`
\end{eqnarray}

```


| m  |  d | q  | r  | 実数除算 | 絶対値除算 | 例    |商  | 余  |
|:--:|:--:|:--:|:--:|:-------:|:----------:|:-----:|:--:|:---:| 
| 正 | 正 | 正 | 正 | floor   | floor      |  10÷3  | 3 |  1  |
| 正 | 負 | 負 | 正 | ceil    | floor      | 10÷-3  |-3 |  1  |
| 負 | 正 | 負 | 負 | ceil    | floor      | -10÷3  |-3 | -1  |
| 負 | 負 | 正 | 負 | floor   | floor      | -10÷-3 | 3 | -1  |

実数除算は、0方向への切り捨て(tranc)になる。
 *)

(**
## 剰余が除数と同符号（Python ``%``演算子）

```math
\begin{eqnarray}
0 \le  r \lt d \\
d \lt  r \le 0 \\
\end{eqnarray}

```

| m  |  d | q  | r  | 実数除算 | 絶対値除算 | 例    |商  | 余  |
|:--:|:--:|:--:|:--:|:-------:|:----------:|:-----:|:--:|:---:| 
| 正 | 正 | 正 | 正 | floor   | floor      |  10÷3  | 3 |  1  |
| 正 | 負 | 負 | 負 | floor   | ceil       | 10÷-3  |-4 | -2  |
| 負 | 正 | 負 | 正 | floor   | ceil       | -10÷3  |-4 |  2  |
| 負 | 負 | 正 | 負 | floor   | floor      | -10÷-3 | 3 | -1  |
*)

(**
## 剰余が商と同符号

```math
\begin{eqnarray}
0 \le  r \lt d, ただし q \ge 0 \\
d \lt -r \le 0, ただし q \lt 0 \\
\end{eqnarray}

```

| m  |  d | q  | r  | 実数除算 | 絶対値除算 | 例    |商  | 余  |
|:--:|:--:|:--:|:--:|:-------:|:----------:| -----:|:--:|:---:| 
| 正 | 正 | 正 | 正 | floor   | floor      |  10÷3  | 3 |  1  |
| 正 | 負 | 負 | 負 | floor   | ceil       | 10÷-3  |-4 | -2  |
| 負 | 正 | 負 | 負 | ceil    | floor      | -10÷3  |-3 | -1  |
| 負 | 負 | 正 | 正 | ceil    | ceil       | -10÷-3 | 4 |  2  |
*)

(**
## 剰余が負（使えない）

これは、式(2.2)と式(2.4)を使う。これをまとめると、次の式になる。
$$ | d | \lt r \le 0| $$

| m  |  d | q  | r  | 実数除算 | 絶対値除算 | 例    |商  | 余  |
|:--:|:--:|:--:|:--:|:-------:|:----------:| -----:|:--:|:---:| 
| 正 | 正 | 正 | 負 | ceil    | ceil       |  10÷3  | 4 | -2  |
| 正 | 負 | 負 | 負 | floor   | ceil       | 10÷-3  |-4 | -2  |
| 負 | 正 | 負 | 負 | ceil    | floor      | -10÷3  |-3 | -1  |
| 負 | 負 | 正 | 負 | floor   | floor      | -10÷-3 | 3 | -1  |
*)

(**
## 剰余が絶対値で最小（Cの``remainder``関数）

| m  |  d | q  | r  | 実数除算 |
|:--:|:--:|:--:|:--:|:-------:|
| 正 | 正 | 正 | * | round    |
| 正 | 負 | 負 | * | round    |
| 負 | 正 | 負 | * | round    |
| 負 | 負 | 正 | * | round    |

* 余りは、正または負で、絶対値が最小となる値。
*)

(**
# 使用しなかった補題
 *)
Section OPT.
  
  (* intidiv.v の補題 を使って証明する。 *)
  Lemma divn_eq'' (m d : nat) : m = (m %/ d * d)%N%:Z + (m %% d)%N :> int.
  Proof.
    Check divz_eq : forall m d : int, m = (m %/ d)%Z * d + (m %% d)%Z.
    
    rewrite {1}(divz_eq m d).
    Search _ (_ + _ = _%N + _%N).
    
    f_equal.
    - by rewrite divz_nat.
    - by rewrite modz_nat.
  Qed.
  
  (* ssrnum の norm の補題を使用することにした。 *)
  Lemma eq_abs (x : int) : 0 <= x -> x = `|x|.
  Proof. by move/normr_idP. Qed.

  Lemma ltz_m_abs (x : int) : x < 0 -> x = - `|x|.
  Proof.
    Set Printing All.
    move=> H.
    rewrite ltr0_norm //=.
      by rewrite opprK.
  Qed.







(* END *)
(* END *)
(* END *)
(* END *)
(* END *)
(* END *)
(* END *)
(* END *)
(* END *)
(* END *)
(* END *)
(* END *)
(* END *)


(**
# （予備）MathComp での定義との同値の証明
 *)
Print divz.
(* 
divz = 
fun m d : int =>
let
'(K, n) := match m with
           | Posz n => (Posz, n)
           | Negz n => (Negz, n)
           end in sgz d * K (n %/ `|d|)%N
 *)

Compute edivz (- 10%:Z) 1.                  (* -10 *)
Compute edivz (- 10%:Z) 2.                  (* -5 *)
Compute edivz (- 10%:Z) 3.                  (* -4 *)
Compute edivz (- 10%:Z) 4.                  (* -3 *)
Compute edivz (- 10%:Z) 5.                  (* -2 *)
Compute edivz (- 10%:Z) 6.                  (* -2 *)
Compute edivz (- 10%:Z) 7.                  (* -2 *)
Compute edivz (- 10%:Z) 8.                  (* -2 *)
Compute edivz (- 10%:Z) 9.                  (* -2 *)
Compute edivz (- 10%:Z) 10.                 (* -1 *)

Compute edivz (- 10%:Z) (- 1%:Z).           (* 10 *)
Compute edivz (- 10%:Z) (- 2%:Z).           (* 5 *)
Compute edivz (- 10%:Z) (- 3%:Z).           (* 4 *)
Compute edivz (- 10%:Z) (- 4%:Z).           (* 3 *)
Compute edivz (- 10%:Z) (- 5%:Z).           (* 2 *)
Compute edivz (- 10%:Z) (- 6%:Z).           (* 2 *)
Compute edivz (- 10%:Z) (- 7%:Z).           (* 2 *)
Compute edivz (- 10%:Z) (- 8%:Z).           (* 2 *)
Compute edivz (- 10%:Z) (- 9%:Z).           (* 2 *)
Compute edivz (- 10%:Z) (- 10%:Z).          (* 1 *)

Compute divz (- 10%:Z) 1.                  (* -10 *)
Compute divz (- 10%:Z) 2.                  (* -5 *)
Compute divz (- 10%:Z) 3.                  (* -4 *)
Compute divz (- 10%:Z) 4.                  (* -3 *)
Compute divz (- 10%:Z) 5.                  (* -2 *)
Compute divz (- 10%:Z) 6.                  (* -2 *)
Compute divz (- 10%:Z) 7.                  (* -2 *)
Compute divz (- 10%:Z) 8.                  (* -2 *)
Compute divz (- 10%:Z) 9.                  (* -2 *)
Compute divz (- 10%:Z) 10.                 (* -1 *)

Compute divz (- 10%:Z) (- 1%:Z).           (* 10 *)
Compute divz (- 10%:Z) (- 2%:Z).           (* 5 *)
Compute divz (- 10%:Z) (- 3%:Z).           (* 4 *)
Compute divz (- 10%:Z) (- 4%:Z).           (* 3 *)
Compute divz (- 10%:Z) (- 5%:Z).           (* 2 *)
Compute divz (- 10%:Z) (- 6%:Z).           (* 2 *)
Compute divz (- 10%:Z) (- 7%:Z).           (* 2 *)
Compute divz (- 10%:Z) (- 8%:Z).           (* 2 *)
Compute divz (- 10%:Z) (- 9%:Z).           (* 2 *)
Compute divz (- 10%:Z) (- 10%:Z).          (* 1 *)



Check gez0_abs.
Check gtz0_abs.
Check lez0_abs.
Check ltz0_abs.

Check divz_nat : forall m d : nat, (m %/ d)%Z = (m %/ d)%N.

Check divzN.
Lemma divz_nat1 (m d : nat) : divz m (- d%:Z) = - divz m d.
Proof. by rewrite divzN. Qed.

Lemma divz_nat2 (m d : nat) : divz (- m%:Z) d = - divz m d.
Proof.
  Admitted.

Lemma divz_nat3 (m d : nat) : divz (- m%:Z) (- d%:Z) = divz m d.
Proof.
  Admitted.


Lemma edivz_nat (m d : nat) : edivz m d = (m %/ d)%N.
Proof. by case: d => // d; rewrite /edivz /= mul1r. Qed.

Lemma edivz_nat1 (m d : nat) : edivz m (- d%:Z) = - edivz m d.
Proof.
  rewrite /edivz.
  case Hm : (0%:Z <= m) => //=.
    by rewrite /edivn_floor abszN sgzN mulNr.
Qed.

Lemma test (m : nat) : (0 <= - m%:Z) = true -> (m = 0)%N.
Proof. Admitted.

Lemma edivz_nat2 (m d : nat) : edivz (- m%:Z) d = - edivz m d.
Proof.
  rewrite /edivz.
  case Hm : (0%:Z <= - m%:Z) => //=.
  - move/test in Hm.                        (* 両辺は0 *)
    rewrite Hm.
    rewrite /edivn_floor.
    rewrite abszN.
    rewrite div0n.
      by rewrite mulr0.
  - f_equal.
    f_equal.
    f_equal.
    (* 0 < m -> edivn_ceil `|- m| d = edivn_floor m d *)
    rewrite /edivn_floor /edivn_ceil.
    case H : (d %| `|- m%:Z|)%N.
    + admit.
    + f_equal.
      f_equal.
      f_equal.
    (* (`|- m| %/ d).+1 = (m %/ d)%N *)
  Admitted.

Lemma edivz_nat3 (m d : nat) : edivz (- m%:Z) (- d%:Z) = edivz m d.
Proof.
  rewrite /edivz.
  case Hm : (0%:Z <= - m%:Z) => //=.
  - move/test in Hm.                        (* 両辺は0 *)
    rewrite Hm.
    rewrite /edivn_floor.
    rewrite abszN div0n.                    (* 左辺が0にならない。 *)
    admit.
  - rewrite /edivn_floor /edivn_ceil.
    case H : (`|- d%:Z| %| `|- m%:Z|)%N.
    + admit.
    + f_equal.
      
Admitted.
    

Lemma divz_edivz (m d : int) : d != 0 -> divz m d = edivz m d.
Proof.
  move=> Hd.
  case Hm : (0 <= m); case H : (0 <= d).
  - rewrite -(gez0_abs Hm).
    rewrite -(gez0_abs H).
    rewrite divz_nat.
    rewrite edivz_nat.
    done.
  - move/nge_lt in H.
    rewrite -(gez0_abs Hm).
    rewrite -(opptr (ltz0_abs H)).
    rewrite divz_nat1 divz_nat.
    rewrite edivz_nat1 edivz_nat.
    done.
  - move/nge_lt in Hm.
    rewrite -(opptr (ltz0_abs Hm)).
    rewrite -(gez0_abs H).
    rewrite divz_nat2 divz_nat.
    rewrite edivz_nat2 edivz_nat.
    done.
  - move/nge_lt in Hm.
    move/nge_lt in H.
    rewrite -(opptr (ltz0_abs Hm)).
    rewrite -(opptr (ltz0_abs H)).
    rewrite divz_nat3 divz_nat.
    rewrite edivz_nat3 edivz_nat.
    done.
Qed.

Lemma test (n d k : nat) : (d %| n)%N -> (k < d)%N -> (n %/ d = (n + k) %/ d)%N.
Proof.
  move=> Hnd Hkd.
  rewrite addnC.
  rewrite divnDr //.
  rewrite (divn_small Hkd).
    by rewrite add0n.
Qed.

Lemma test' (n d k : nat) : (d %| n)%N -> (k < d)%N -> (((n - k) %/ d).+1 = n %/ d)%N.
Proof.
  move=> Hnd Hkd.
  Admitted.

Lemma test'' (n d k1 k2 : nat) : (d %| n)%N -> (k1 < k2 < d)%N ->
                                 ((n - k1) %/ d = (n - k2) %/ d)%N.
Proof.
  move=> Hnd Hkd.
  Admitted.

Lemma test1 (n d : nat) :
  (d %| n.+1)%N -> ((n %/ d).+1 = (n.+1 %/ d))%N.
Proof.
  Search _ (_  %/ _ <= _)%N.
  move=> Hd.
  Check @test' n.+1 d 1.
  rewrite -(@test' n.+1 d 1) //=.
  rewrite subn1 -pred_Sn.
  done.
Admitted.

Lemma test2 (n d : nat) :
  ~~(d %| n.+1)%N -> ((n %/ d) = (n.+1 %/ d))%N.
Proof.
  move=> H.
Admitted.

Lemma divz_edivz (m d : int) : d != 0 -> divz m d = edivz m d.
Proof.
  move=> Hd.
  rewrite /divz /edivz.
  case: m => n /=.
  - done.
  - rewrite /edivn_ceil.
    case H3 : (`|d| %| `|Negz n|)%N.
    + rewrite -mulrN.
      rewrite ssrint.NegzE in H3.
      rewrite intOrdered.abszN in H3.
      f_equal.
      rewrite ssrint.NegzE.
      f_equal.
      f_equal.
      (* (n %/ `|d|).+1 = (n.+1 %/ `|d|)%N *)
        by rewrite test1 //=.

    + rewrite -mulrN.
      rewrite ssrint.NegzE in H3.
      rewrite intOrdered.abszN in H3.
      move/negbT in H3.
      f_equal.
      rewrite ssrint.NegzE.
      f_equal.
      f_equal.
      f_equal.
      (* (n %/ `|d|)%N = (n.+1 %/ `|d|)%N *)
        by rewrite test2 //=.
Qed.

(**
Lemma edivz_nat (n d : nat) : (edivz n d)%Z = (n %/ d)%N.
Proof. by case: d => // d; rewrite /edivz /= mul1r. Qed.

Lemma edivzN m d : (edivz m (- d))%Z = - (m %/ d)%Z.
Proof.
  case H : (0 <= m).
  - rewrite /edivz H.
    rewrite /edivn_floor.
    rewrite sgzN.
    rewrite mulNr.
Admitted.

Lemma edivzN' m d : (edivz (- m) d)%Z = - (m %/ d)%Z.
Proof.
Admitted.


Lemma divzN' m d : (- m %/ d)%Z = - (m %/ d)%Z.
Proof. Admitted.

Lemma divz_edivz (m d : int) : d != 0 -> divz m d = edivz m d.
Proof.
  move=> Hd.
  case Hm : (0 <= m); case H : (0 <= d).
  - admit.
  - ree
  

*)


Check ltn_pmod : forall m d : nat, (0 < d)%N -> (m %% d < d)%N.
Lemma ediv_mod_ltd (m d : int) : d != 0 -> emodz m d < `|d|.
Proof.
  move=> Hd.
  rewrite /emodz /edivz.
  case: ifP => Hm; case H : (0 <= d).
  - rewrite -mulrAC.
    rewrite -abszEsg mulrC.
    rewrite /edivn_floor.
    (* m - (`|m| %/ `|d|)%N * `|d|%N < `|d| *)
    admit.
  - rewrite -mulrAC.
    rewrite -abszEsg mulrC.
    rewrite /edivn_floor.
    (* m - (`|m| %/ `|d|)%N * `|d|%N < `|d| *)
    admit.
  - rewrite opprK.
    

rewrite -mulrAC.
    rewrite -abszEsg mulrC.
    rewrite /edivn_floor.
    

    
  
  - rewrite -mulrAC.
    rewrite -abszEsg mulrC.
    rewrite -subr_lt0.
    move/normr_idP in H.
    
    rewrite -{2}H.
    apply: edivn_floorp.

    

    rewrite subr_ge0.
    move/normr_idP in H.
    rewrite -{2}H.
      by apply: edivn_floorp.

  - rewrite mulNr.
    (* m - - X は m + (- - X) なので、二重の負号 oppz を消します。 *)
    rewrite [- - (sgz d * edivn_ceil `|m| `|d| * d)]oppzK.
    rewrite -mulrAC.
    rewrite -abszEsg mulrC.
    move/nge_lt in H.
    rewrite {1}(ltz_m_abs H).
    rewrite addrC subr_ge0.
    apply: edivn_ceilp.
      by rewrite -lt0n absz_gt0.
  
  


      