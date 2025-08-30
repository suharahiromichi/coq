(**
整数除算と剰余演算について - ユーグリッド除法 Euclidean division を中心に
========================

@suharahiromichi

2020/08/25

2023/04/29 Coq 8.17.0 (order.v)
 *)

(**
# はじめに

## 形式化

小学校で習う整数の剰余付き除算は、次に示す式(1.1)から(1.3)を満たす
整数 m, d, q, r に対して、与えられた m, d から q, r を求めること、と形式化できます。


```math
\begin{eqnarray}
d &\ne& 0               \tag{1.1} \\

m &=& q d + r           \tag{1.2} \\

| r | &\lt& | d |       \tag{1.3} \\
\end{eqnarray}

```

ここで、m を被除数、d を除数、q を商、r を剰余または余り、と呼びます。

## 一意性の問題

しかし、式(1.3)から分かるとおり、この定式化では d, rは一意に決まりません。

具体的にいうと、$ 10 \div 3 $ の結果が 3 余り 1 でも、4 余り -2 であっても
式を満たすからです。
このことが、プログラミング言語の C と Python と Pascal とで、
剰余計算の結果が異なることの理由です。

一意性を担保するには、剰余の範囲をより狭く制限する必要があります。
たとえば、教科書に記載されるのは、

$$ 0 \le r \lt | d | \tag{1.3'} $$

のように、剰余を正の範囲に制限することで、これをユーグリッド除法と呼びます。
これは、プログラミング言語Pascalの ``mod`` 演算で採用されています。
また Coq/MathComp の ``divz`` もこの定義です。


## 商と剰余の求める方法

一方、商 q を求めるには、いくつかの方法があります。

- ``m / d`` を実数で求め、切り捨てまたは切り上げして、qとする。
- ``|m| / |d|`` と絶対値で求め、切り捨てまたは切り上げ(注1)して、
符号を復元して(注2)、qとする。



(注1) 自然数の除算における切り捨てと切り上げは後で定義します。

(注2) m と d と q の負号は、偶数個の関係にあります。


剰余 r は式(1.2)から求めます。

このほか 減算を繰り返す方法もありますが、自然数の除算自体は減算で定義されるものとして、
それに含めることにします。


## ユーグリッド除法

ここでは、剰余が式(1.3')を満たすものとし、ユーグリッド除法、すなわち、
計算式としては、絶対値の除算を使う方法を採用します。そして、


- 式(1.3')の制限を加えると、qとrが一意に決まることを証明する。

- q と r を求める式を具体的に定義して、式(1.2)と式(1.3')が成り立つことを証明する。


これによって、整数除算が持つ意味の健全性を示すことができるはずです。
証明には Coq/MathComp を使います。
MathCompにも``intdiv.v``で整数除算が定義されていますが、ここでは独自に実装してみます。

最後に、ここで示した以外の整除法について言及します。

このファイルは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_ediv.v

証明スクリプトは模範回答ではなく、一例として参考程度にしてください。
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Import Order.Theory.         (* 不等号関連 *)

Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)

(**
# 整数について

## 概説

int は、natとちがって、MathCompの型クラス階層の中で、zmodType、ringType、comRingType
のインスタンスとして定義されています。int_ZmodType、int_Ring、int_ComRing。

そのため、以下に注意が必要です。

- 四則演算や剰余算については、当然定義がことなり、文脈（スコープ）によって選ばれます。

- 加算、負号、乗算は環などの演算のインスタンスですから、環についての補題が使えます。

- 減算は ``x - y = x + (- y)`` のように、加算の構文糖衣なので、加算についての補題が使えます。


さらにに注意するべきなのは絶対値記号です。``ssrint.v``で定義される絶対値記号は、
``absz : int -> nat`` の型で nat_scope で定義されています。
そのため、整数の文脈では `` `|n|%N `` と記載する必要があります。

一方、整数の文脈のディフォルト `` `|x|%Z `` は、環で定義された ``normr T:R : T -> T`` に
整数を適用した ``normr : int -> int`` です。

本資料では、絶対値は absz の方を使うことにして、`` `|n|%N `` のように ``%N``を必ず付ける
ことにします。
 *)
(**
### m n : nat のときの m = n とはどういう意味か

等号 ``=`` は、自然数の文脈では ``eq nat``、整数の文脈では ``eq int`` です。
m と n が自然数なので、整数文脈では、自然数から正整数へのコアーションが行われます。
つまり Posz (``%:Z`` とおなじ) が埋め込まれるわけです。
 *)
Section INTRO.
  Variables m n : nat.

  (* 自然数文脈 *)
  Check @eq nat m n.
  Check (m = n)%N.
  
  (* 整数文脈、つぎの四者は同じ式の構文糖衣 *)
  Check @eq int (Posz m) (Posz n).
  Check Posz m = Posz n.
  Check m%:Z = n%:Z.
  Check m = n :> int.
  
(**
自然数文脈で等しければ整数文脈でも等しいので、両者は同値です（eqz_nat 補題）。
*)
  Check eqz_nat m n : (m == n :> int) = (m == n)%N.

(**
自然数型の式を整数型の式に書き換えることはできませんが（型が違うので）、
この補題を使って、
自然数の文脈の等式を整数の文脈の等式に書き換えるとは可能です。
等式はどちらもbool型だからです。
 *)
End INTRO.

(**
### 整数演算と自然数演算の変換（``%:Z``の分配則）

整数の文脈の中で自然数を書くと、自然数から正整数のコアーションが起きます。
（Posz あるいは ``%:Z`` が補われます）。

%Nで自然数のスコープを明示できますが、この外に出た時点で、
同様にコアーションで正整数になります。
また、自然数でも正整数でも演算の結果は同じですから、``%:Z`` は分配できるわけです。

ただし、addやsubやleやltやdivやmodの演算は、定義そのものは、
整数と自然数でまったく別であることに注意してください。
 *)

Section INT.
  Variables m n d : nat.
  
  (* 左辺は自然数の加算、右辺は整数の加算であり、ディフォルトの環（整数）で比較している。 *)
  Check PoszD m n : (m + n)%N%:Z = m%:Z + n%:Z. (* m + n = (m + n)%N と見える。 *)
  Check PoszM m n : (m * n)%N%:Z = m%:Z * n%:Z. (* (m * n)%N = m * n *)

  Check subzn : forall m n : nat, (n <= m)%N -> m%:Z - n%:Z = (m - n)%N%:Z.
  Check divz_nat n d : (n %/ d)%Z = (n %/ d)%N%:Z.
  Check modz_nat m d : (m %% d)%Z = (m %% d)%N%:Z.
  Check lez_nat m n : (m%:Z <= n%:Z) = (m <= n)%N. (* 両辺はbool *)
  Check ltz_nat m n : (m%:Z < n%:Z) = (m < n)%N.   (* 両辺はbool *)
  
  Variables x y : int.
  Check oppzD x y : - (x + y) = -x + -y.
End INT.

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
Lemma eq_eqabsabs (x y : int) : x = y -> `|x|%N = `|y|%N.
Proof. by move=> ->. Qed.

(* いつも欲しくなる補題の整数版 *)
Lemma lt_le (x y : int) : x < y -> x <= y.
Proof.
  rewrite le_eqVlt => H.                    (* ler_eqVlt から改名 *)
  by apply/orP/or_intror.  
Qed.

Lemma nge_lt (m n : int) : (m <= n) = false -> n < m.
Proof.
  move/negbT.
  by rewrite ltNge.                         (* ltnNge から改名 *)
Qed.

Lemma eq_subn (n : nat) : (n - n = 0)%N.    (* 自然数の補題 *)
Proof. apply/eqP. by rewrite subn_eq0. Qed.

Lemma eq_subz (x : int) : x - x = 0.        (* 整数の補題 *)
Proof. by rewrite addrC addNr. Qed.

(**
自然数の除算について、商と被除数の積と剰余の和が除数になる補題が証明されています。
*)
Check divn_eq : forall m d : nat, m = (m %/ d * d + m %% d)%N.
(**
同じ補題を整数スコープで証明しておくと便利です。
*)
Lemma divn_eq' (m d : nat) : m = (m %/ d * d)%N%:Z + (m %% d)%N%:Z :> int.
Proof.
  apply/eqP.
  by rewrite eqz_nat -divn_eq.
Qed.

(**
### 絶対値を操作する補題
 *)
Section ABS.
  Variable m : nat.
  Variable x : int.
(**
自然数の文脈と整数の文脈とで関数が異なるので、注意が必要です。
 *)
  Check absz : int -> nat.                  (* |x|%N *)
  Check Num.Def.normr : int -> int.         (* |x|%Z *)
(**
normr は、環一般について定義されています。
 *)

(**
両者の結果は、自然数から正整数へのコアーションで等しい。
*)  
  Check abszE x : `|x|%N%:Z = `|x|%:Z.      (* `|x|%N = `|x| *)
  
(**
- absz
*)  
  (* 自然数 *)
  Check absz_nat m : `| m%:Z |%N = m.       (* `|m|%N = m *)
  (* 正整数 *)
  Check gez0_abs : forall x : int, 0 <= x -> `|x|%N = x :> int. (* `|x|%N = x *)
  Check gtz0_abs : forall x : int, 0 < x -> `|x|%N = x :> int.
  (* 負整数 *)
  Check lez0_abs : forall x : int, x <= 0 -> `|x|%N = - x :> int.  
  Check ltz0_abs : forall x : int, x < 0 -> `|x|%N = - x :> int.  
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

Section NORM.
  Variable x : int.
(**
- norm

実際の証明では、norm は使わないようにしたので、以下は不使用である。
*)
  (* 自然数 *)
  Lemma norm_nat (n : nat) : `| n%:Z | = n%:Z. (* `|n| = n *)
  Proof. by rewrite -abszE absz_nat. Qed.
  (* 正整数 *)
  Check @ger0_norm int x : 0 <= x -> `|x| = x :> int. (* `|x| = x *)
  Check @gtr0_norm int x : 0 < x -> `|x| = x :> int.
  (* 負整数 *)
  Check @ler0_norm int x : x <= 0 -> `|x| = - x :> int.
  Check @ltr0_norm int x : x < 0 -> `|x| = - x :> int.
End NORM.

Lemma normq0_eq (x y : int) : `|x - y| = 0  <-> x = y.
Proof.
  split=> H.
  Check @normr0P : forall (R : numDomainType) (V : normedZmodType R) (v : V), reflect (`|v| = 0) (v == 0).
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

切り捨て(floor)除算と、切り上げ(ceil)除算の二種類です。

切り捨て除算は、自然数で定義された除算 (divn) とおなじです。

```math
\lfloor m / d \rfloor = divn(m, d)

```

切り上げ除算は、divn の結果に``+1``します。ただし、mがdで割り切れる場合はそのまま、
mがdで割りきれない場合は``+1``します。 
$ d \setminus m $ は、 m は dで割りきれることを示し、
$ d \not \setminus m $ は、m は dで割りきれないことを示します。
``除数 \ 被除数`` の順番であることに注意してください。

```math
\lceil m / d \rceil =
\left\{
\begin{array}{ll}
divn(m, d) & (但し d \setminus m) \\
divn(m, d) + 1 & (但し d \not \setminus m)
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

- 切り捨て除算の場合は被除数以下
- 切り上げ除算の場合は被除数以上


になります。
切り上げにおいて、等号が成立するのはmがdで割り切れる場合で、
そうでない場合は被除数未満となります。このふたつの条件をあわせて補題にしています。

```math
\lfloor m / d \rfloor d \le m
```
```math
\lceil m / d \rceil d \ge m
```

これを補題として証明しておきます。
*)
Lemma edivn_floorp (m d : nat) : (edivn_floor m d * d <= m)%N.
Proof.
  rewrite /edivn_floor.
  by apply: leq_trunc_div.
Qed.

Lemma edivn_ceilp (m d : nat) : (0 < d)%N -> (m <= edivn_ceil m d * d)%N.
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
    by rewrite ltn_ceil //.
Qed.

(**
ついで、商と除数の積と被除数の差が、除数未満であることを証明します。

```math
m - \lfloor m / d \rfloor d \lt d
```
```math
\lceil m / d \rceil d - m   \lt d
```
*)
Lemma edivn_floor_ltd (m d : nat) : (0 < d)%N ->
                                    m%:Z - (edivn_floor m d * d)%:Z < d.
Proof.
  move=> Hd.
  rewrite /edivn_floor.
  rewrite {1}(divn_eq' m d).
  rewrite -addrAC eq_subz add0r.
  Check ltn_pmod : forall m d : nat, (0 < d)%N -> (m %% d < d)%N.
  by apply: ltn_pmod.
Qed.

Lemma edivn_ceil_ltd (m d : nat) : (0 < d)%N ->
                                   (edivn_ceil m d)%:Z * d - m%:Z < d.
Proof.
  move=> Hd.
  rewrite /edivn_ceil.
  rewrite {1}(divn_eq' m d).
  case: ifP => H.
  (* m が d で、割り切れるので m %% d = 0 の場合 *)
  - move/eqP in H.
    rewrite H /= addr0.
    by rewrite eq_subz.
  (* m が d で、割りきれない場合 *)
  - rewrite opprD addrCA addrA -addn1.
    have l_dist (m' : nat) : (m' + 1)%N%:Z * d = (m' * d)%N%:Z + d
      by apply/eqP; rewrite eqz_nat mulnDl mul1n.
    rewrite l_dist //= addrA [- _ + _]addrC.
    rewrite eq_subz add0r ltrBDl ltrDr.
    rewrite ltz_nat lt0n.
    (* Goal : (m %% d)%N != 0 *)
    rewrite /dvdn in H.
    by move/negbT in H.
Qed.

(**
## ユーグリッド除算の定義

直感的に説明するのが難しいので、数直線でも書いて納得してほしいのですが、
整数のユーグリッド除算を絶対値の除算で求める場合、
商は次のように求めると、剰余を正とすることができます。

- 被除数が正なら絶対値の除算で切り捨てしたあと除数の符号を反映します。
- 被除数が負なら絶対値の除算で切り上げしたあと除数の符号を反映し、さらに符号を反転します。

```math
m / d =
\left\{
\begin{array}{ll}
(sgz\ d) \lfloor |m| / |d| \rfloor & (m \ge 0) \\
- (sgz\ d) \lceil |m| / |d| \rceil & (m \lt 0) \\
\end{array}
\right.
```

ここで、sgz は符号関数です。

剰余は、被除数から商と除数の積を引いて求めます。これは整数で計算します。

```math
m\ mod\ d = m - (m / d) d
```
 *)
Definition edivz (m d : int) : int :=
  if (0 <= m) then
    sgz d * (edivn_floor `|m|%N `|d|%N)
  else
    - (sgz d * (edivn_ceil `|m|%N `|d|%N)).

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
定義から自明ですが、式(1.2)も成り立っています。
*)
Lemma edivz_eq (m d : int) : m = (edivz m d)%Z * d + (emodz m d)%Z.
Proof.
  by rewrite addrC subrK.
Qed.

(**
# 式(1.3')の証明

先に、比較的やさしいほうの証明をします。証明するべきは以下です。

```math
0 \le m\ mod\ d \lt | d |
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
  (* 0 <= m の場合 *)
  - rewrite -mulrAC -abszEsg mulrC subr_ge0.
    move/gez0_abs in H.
    rewrite -{2}H.
    (* edivn_floor `|m| `|d| * `|d|%N <= `|m| *)
    by apply: edivn_floorp.

  (* 0 > m の場合 *)
  (* よく見るとわかりますが、右辺の負号は括弧だけに掛かっているので、
     右から掛けるdを中に入れます。 *)
    Check m - (- (sgz d * edivn_ceil `|m| `|d|)) * d.
    Check mulNr : forall (R : ringType) (x y : R), - x * y = - (x * y).
  - rewrite mulNr.
    (* m - - X は m + (- - X) なので、二重の負号 oppz を消します。 *)
    rewrite [- - _]oppzK -mulrAC -abszEsg mulrC.
    move/nge_lt in H.
    Check opptr (ltz0_abs H) : - `|m|%N%:Z = m.
    rewrite -{1}(opptr (ltz0_abs H)).
    rewrite addrC subr_ge0.
    (* `|m| <= edivn_ceil `|m| `|d| * `|d|%N *)
    apply: edivn_ceilp.
    (* (0 < `|d|)%N *)
    by rewrite lt0n absz_eq0.
Qed.

(**
## 定理 - 剰余は除数より小
 *)
Lemma ediv_mod_ltd (m d : int) : d != 0 -> emodz m d < `|d|%N.
Proof.
  move=> Hd.
  rewrite /emodz /edivz.
  case: ifP => Hm; case H : (0 <= d).
  (* m が、0 <= m か 0 > m か、
     d が、0 <= d か 0 > d か、で場合分けする。 *)
  
  (* Goal : m - sgz d * edivn_floor `|m| `|d| * d < `|d| *)
  - rewrite mulrAC -abszEsg mulrC.          (* 商*除数の部分 *)
    rewrite -{1}(gez0_abs Hm).              (* 被除数の部分 *)
    apply: edivn_floor_ltd.                 (* 自然数割算の補題 *)
    by rewrite -absz_gt0 in Hd.
    
  (* Goal : m - sgz d * edivn_floor `|m| `|d| * d < `|d| *)    
  - rewrite mulrAC -abszEsg mulrC.
    rewrite -{1}(gez0_abs Hm).
    apply: edivn_floor_ltd.
    by rewrite -absz_gt0 in Hd.
  (* by rewrite -normr_gt0 in Hd. *)
    
  (* Goal : m - - (sgz d * edivn_ceil `|m| `|d|) * d < `|d| *)    
  - rewrite mulNr mulrAC -abszEsg mulrC opprK.
    move/nge_lt in Hm.
    rewrite -{1}(opptr (ltz0_abs Hm)) addrC.
    apply: edivn_ceil_ltd.
    by rewrite -absz_gt0 in Hd.
      
  (* Goal : m - - (sgz d * edivn_ceil `|m| `|d|) * d < `|d| *)
  - rewrite mulNr mulrAC -abszEsg mulrC opprK.
    move/nge_lt in Hm.
    rewrite -{1}(opptr (ltz0_abs Hm)) addrC.
    apply: edivn_ceil_ltd.
    by rewrite -absz_gt0 in Hd.
Qed.

(**
まとめると、式(1.3')が成り立つことが証明できます。
*)
Lemma ediv_mod_ge0_ltd (m d : int) : d != 0 -> 0 <= emodz m d < `|d|%N.
Proof.
  move=> hd.
  apply/andP; split.
  - by apply: ediv_mod_ge0.
  - by apply: ediv_mod_ltd.
Qed.


(**
# 一意性の証明

式(1.2)と式(1.3)を満たす商qと剰余rがふたつあったとして、それが等しいことを証明します。
すなわち、

```math
\left\{
\begin{array}{ll}
m = q_{1} d + r_{1} \\
m = q_{2} d + r_{2} \\
\end{array}
\right.
```

のとき、

```math
\left\{
\begin{array}{ll}
q_{1} = q_{2} \\
r_{1} = r_{2} \\
\end{array}
\right.
```

であることを証明します。先に $ q_{1} = q_{2} $ を証明し、
ついで、$ r_{1} = r_{2} $ を証明します。
*)

(**
補題： 自然数 q と d の積が d より小さいなら、q は0である。

実数なら q は 1未満となるわけですが、自然数なので q は0になります。
*)
Lemma lemma1 (q d : nat) : (q * d < d)%N -> (q = 0)%N.
Proof.
  rewrite -{2}[d]mul1n.
  Check ltn_mul2r
    : forall m n1 n2 : nat, (n1 * m < n2 * m)%N = (0 < m)%N && (n1 < n2)%N.
  rewrite ltn_mul2r.
  move/andP => [Hd Hq].
  move: Hq.
  have -> : (q < 1)%N = (q <= 0)%N by done.
(*
  Locate "m < n".                           (* m.+1 <= n *)
  (* Hq : q + 1 < 1 *)
  rewrite -addn1.
  have H : (1 = 0 + 1)%N by done.
  rewrite {2}H.
  Search _ ((_ + _ <= _ + _)%N).
  rewrite leq_add2r.
  Search _ ((_  <= 0)%N).
*)
  rewrite leqn0.
  move/eqP.
  done.
Qed.

(**
補題：``q1 * d + r1 = q2 * d + r2`` のとき、移項して絶対値で``=``をとる。
*)
Lemma lemma3 (q1 q2 r1 r2 d : int) :
  q1 * d + r1 = q2 * d + r2 -> `|((q1 - q2) * d)%R|%N = `|r1 - r2|%N.
Proof.
  (* 前提 *)
  move/eqP.
  Check subr_eq : forall (V : zmodType) (x y z : V), (x - z == y) = (x == y + z).
  rewrite -subr_eq -addrA addrC eq_sym -subr_eq -mulrBl -[(q2 - q1)]opprB.
  (* Goal : - (q1 - q2) * d = r1 - r2 *)
  
  move/eqP/eq_eqabsabs.           (* 前提の両辺に絶対値記号をつける。 *)
  rewrite mulNr abszN.            (* 前提左辺の絶対値の負号を消す。 *)
  done.
Qed.

(**
補題：
*)
Lemma lemma2 (r1 r2 : int) (d : nat) :
  0 <= r1 < d -> 0 <= r2 < d -> `|r1 - r2|%N < d :> int.
Proof.
  move=> Hr1 Hr2.
  move/andP : Hr1 => [Hr1 Hr1d].
  move/andP : Hr2 => [Hr2 Hr2d].

  move: (ltr_wpDr Hr1 Hr1d) => Hr1dr1.     (* Hr1dr1 : r1 < d + r1 *)
  move: (ltr_wpDr Hr2 Hr1d) => Hr1dr2.     (* Hr1dr2 : r1 < d + r2 *)
  move: (ltr_wpDr Hr1 Hr2d) => Hr2dr1.     (* Hr2dr1 : r2 < d + r1 *)
  move: (ltr_wpDr Hr2 Hr2d) => Hr2dr2.     (* Hr2dr2 : r2 < d + r2 *)
  
  (* r1 と r2 は0以上なので、絶対値記号をつけます。 *)
  Check gez0_abs Hr1 : `|r1|%N%:Z = r1.
  rewrite -(gez0_abs Hr1) in Hr1d.         (* `|r1|%N < d *)
  rewrite -(gez0_abs Hr2) in Hr2d.         (* `|r2|%N < d *)
  rewrite -(gez0_abs Hr1) in Hr1dr1.       (* `|r1|%N < d + `|r1|%N *)
  rewrite -(gez0_abs Hr1) -(gez0_abs Hr2) in Hr1dr2. (* `|r1|%N < d + `|r2|%N *)
  rewrite -(gez0_abs Hr1) -(gez0_abs Hr2) in Hr2dr1. (* `|r2|%N < d + `|r1|%N *)
  rewrite -(gez0_abs Hr2) in Hr2dr2.       (* `|r2|%N < d + `|r2|%N *)
  
  case H : (r1 - r2 >= 0).
  (* r2 <= r1 の場合 *)
  - move: {+}H => H'.                       (* 複製する。 *)
    rewrite -(gez0_abs Hr1) -(gez0_abs Hr2) in H'.
    (* H' : (0 <= `|r1|%N - `|r2|%N) = true *)
    
    move/gez0_abs in H.
    rewrite H -(gez0_abs Hr1) -(gez0_abs Hr2).
    (* H : `|r1 - r2|%N = r1 - r2 *)
    
    have H2 := @ltn_sub2r `|r2| `|r1| (d + `|r2|) Hr2dr2 Hr1dr2.
    rewrite -addnBA in H2 ; last done.
    rewrite (eq_subn `|r2|) in H2.
    rewrite addn0 in H2.
    (* H2 : (`|r1| - `|r2| < d)%N *)
    
    rewrite -ltz_nat -subzn // in H2.
    (* Goal : (`|r2| <= `|r1|)%N *)
    by rewrite -lez_nat -subr_ge0.
      
  (* r1 < r2 の場合 *)
  - move: {+}H => H'.
    rewrite -(gez0_abs Hr1) -(gez0_abs Hr2) in H'.    
    (* H' : (0 <= `|r1|%N - `|r2|%N) = false *)
    
    move/negbT in H.
    rewrite -ltNge in H.                    (* ltrNge から改名 *)
    move/lt_le/lez0_abs in H.
    rewrite H opprB -(gez0_abs Hr1) -(gez0_abs Hr2).
    (* H : `|r1 - r2|%N = - (r1 - r2) *)
    
    have H1 := @ltn_sub2r `|r1| `|r2| (d + `|r1|) Hr1dr1 Hr2dr1.
    rewrite -addnBA in H1 ; last done.
    rewrite (eq_subn `|r1|) in H1.
    rewrite addn0 in H1.
    (* H1 : (`|r2| - `|r1| < d)%N *)
    
    rewrite -ltz_nat -subzn // in H1.
    (* Goal : (`|r1| <= `|r2|)%N *)
    move/nge_lt in H'.
    rewrite subr_lt0 in H'.
    rewrite -lez_nat.
    by apply: lt_le.
Qed.

(**
定理：商 q は一意である。
*)
Lemma edivz_uniqness_q (r1 r2 q1 q2 m d : int) :
  0 <= r1 < `|d| ->
                 0 <= r2 < `|d| ->
                                m = q1 * d + r1 ->
                                m = q2 * d + r2 ->
                                q1 = q2.
Proof.
  move=> Hr1 Hr2 Hq1 Hq2.
  rewrite Hq1 in Hq2.
  apply/abseq0_eq.

  Check @lemma1 `|q1 - q2| `|d| : (`|q1 - q2| * `|d| < `|d|)%N -> `|q1 - q2|%N = 0%N.
  apply: (@lemma1 `|q1 - q2| `|d|).
  
  Check abszM : forall m1 m2 : int, `|(m1 * m2)%R|%N = (`|m1| * `|m2|)%N.
  rewrite -abszM.
  
  Check @lemma3 q1 q2 r1 r2 d Hq2 : `|((q1 - q2) * d)%R|%N = `|r1 - r2|%N.
  rewrite (@lemma3 q1 q2 r1 r2 d Hq2).
  
  by apply: lemma2.
Qed.

(**
定理：剰余 r は一意である。
*)
Lemma edivz_uniqness_r (r1 r2 q m d : int) :
  m = q * d + r1 ->
  m = q * d + r2 ->
  r1 = r2.
Proof.
  move=> -> H.
  rewrite [RHS]addrC [LHS]addrC in H.
  move/eqP in H.
  rewrite -subr_eq in H.
  move/eqP in H.
  rewrite -[LHS]addrA eq_subz addr0 in H.
  done.
Qed.

(**
# 整除法の一覧
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
## 剰余が正（Pascal の ``mod``演算子、ユーグリッド除法）

```math
\begin{eqnarray}
0 \le r \lt d, ただし d \ge 0 \\
d \lt -r \le 0, ただし d \lt 0 \\
\end{eqnarray}

```

このふたつの式は、$|d|$を使ってひとつにまとめられる。これが式(1.3')です。

$$ 0 \le r \lt | d | \tag{1.3'} $$

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
d \lt -r \le 0, ただし m \lt 0 \\
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
$$ | d | \lt r \le 0 $$

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
  
  (* edivz と emodz についても、整数演算から自然数演算に変換できる。 *)
  Lemma edivz_nat (m d : nat) : edivz m d = (m %/ d)%N.
  Proof.
    by case: d => // d; rewrite /edivz /= mul1r.
  Qed.
  
  Lemma emodz_nat (m d : nat) : emodz m d = (m %% d)%N.
  Proof.
    rewrite /emodz edivz_nat.
    rewrite {1}(divn_eq' m d).
    rewrite addrAC eq_subz add0r.
    done.
  Qed.
  
  (* %:Z の分配とみると： *)
  Check edivz_nat : forall (m d : nat), edivz m%:Z d%:Z = (m %/ d)%N%:Z.
  Check emodz_nat : forall (m d : nat), emodz m%:Z d%:Z = (m %% d)%N%:Z.

  (* *** *)
  (* *** *)
  
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
  
  (* ssrnum の norm の補題を直接使用することにした。 *)
  (* さらに、`|x|%N に統一して、norm を使わないようにした。 *)
  Lemma eq_abs (x : int) : 0 <= x -> x = `|x|.
  Proof. by move/normr_idP. Qed.

  Lemma ltz_m_abs (x : int) : x < 0 -> x = - `|x|.
  Proof.
    move=> H.
    rewrite ltr0_norm //=.
    by rewrite opprK.
  Qed.

  (* divn_eq の整数版の別証明 *)
  Lemma divn_eq''' (m d : nat) : m = (m %/ d * d)%N%:Z + (m %% d)%N :> int.
  Proof.
    rewrite /divn modn_def.
    case: edivnP => q r //= Heq Hd.
    rewrite Heq.
    (* Goal : (q * d + r)%N = (q * d)%N + r *)
    done.
  Qed.

  (* edivn_ceil_ltd のミニ補題。自然数の文脈にすると簡単である。 *)
  Lemma l_distr (d m : nat) : (m %/ d + 1)%N%:Z * d = (m %/ d * d)%N%:Z + d.
  Proof.
    apply/eqP.
    rewrite eqz_nat.
    rewrite mulnDl.
    rewrite mul1n.
    done.
  Qed.
End OPT.

(**
# 参考文献

参考になりそうな wikipeida の項目を記載します。

- https://ja.wikipedia.org/wiki/除法

- https://ja.wikipedia.org/wiki/剰余演算

- https://en.wikipedia.org/wiki/Euclidean_division
*)
       
(* END *)
