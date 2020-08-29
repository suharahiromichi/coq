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

$$ 0 \le r \lt | d | $$

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
- q と r を求める式を具体的に定義して、r が0以上であることを証明する。


これによって、整数割算が持つ意味の健全性を示すことができるはずです。
証明には Coq/MathComp を使います。

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
## 補題

MathCompで整数に扱いになれていないひとのために（大抵のひとはそうでしょう）
再利用性のありそうなスクリプトを補題としてまとめておきます。
*)
Lemma nge_lt (m n : int) : (m <= n) = false -> n < m.
Proof.
  move/negbT.
    by rewrite -ltrNge.
Qed.

Lemma ltz_m_abs (m : int) : m < 0 -> m = - `|m|.
Proof.
  move=> H.
  rewrite ltr0_norm //=.
    by rewrite opprK.
Qed.

Lemma abseq0_eq (x y : int) : (`|x - y| = 0)%N  <-> x = y.
Proof.
  split=> H.
  Search _ (`| _ |%N).
  - move/eqP in H.
    Check absz_eq0.
    rewrite absz_eq0 in H.
    Search _ (_ - _ == 0).
    rewrite subr_eq0 in H.
    move/eqP in H.
    done.
  - apply/eqP.
    rewrite absz_eq0 subr_eq0.
    move/eqP in H.
    done.
Qed.

Lemma abseq0_eq' (x y : int) : (`|x - y| = 0)  <-> x = y. (* notu *)
Proof.
  split=> H.
  Search _ (`| _ | = 0).
  - move/normr0P in H.
    rewrite subr_eq0 in H.
    move/eqP in H.
    done.
  - apply/normr0P.
    rewrite subr_eq0.
    apply/eqP.
    done.
Qed.

Lemma eq_eqabsabs (x y : int) : x = y -> (`|x| = `|y|).
Proof.
    by move=> ->.
Qed.

Lemma eq_abs (x : int) : 0 <= x -> x = `|x|.
Proof. by move/normr_idP. Qed.


(* 自然数の補題 *)
Lemma eq_subn n : (n - n = 0)%N.
Proof. apply/eqP. by rewrite subn_eq0. Qed.

Lemma lt_le (x y : int) : x < y -> x <= y.
Proof.
  move=> H.
  Search _ (_ <= _).
  rewrite ler_eqVlt.
    by apply/orP/or_intror.
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
# 剰余が正であることの証明

先に、比較的やさしい剰余が正であることの証明をします。
証明するべきは以下です。

```math
m\ rem\ d \ge 0
```
*)

(**
## 定理

証明はmの正負、すなわち、自然数の除算の切り捨てか切り上げで場合分けしたのち、
自然数の除算の歩再を適用するだけの単純なものです。
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
    rewrite {1}(ltz_m_abs H).
    rewrite addrC subr_ge0.
    apply: edivn_ceilp.
      by rewrite -lt0n absz_gt0.
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
  rewrite (eq_abs Hr1) in Hr1d.
  rewrite (eq_abs Hr2) in Hr2d.
  rewrite (eq_abs Hr1) in Hr1dr1.
  rewrite (eq_abs Hr1) in Hr1dr2.
  rewrite (eq_abs Hr1) in Hr2dr1.
  rewrite (eq_abs Hr2) in Hr1dr2.
  rewrite (eq_abs Hr2) in Hr2dr1.
  rewrite (eq_abs Hr2) in Hr2dr2.

  case H : (r1 - r2 >= 0).
  - move: {+}H => H'.
    rewrite (eq_abs Hr1) in H'.
    rewrite (eq_abs Hr2) in H'.    
    have H'' : `|r2| <= `|r1| by rewrite -subr_ge0.
    
    move/normr_idP in H.
    rewrite H.
    rewrite (eq_abs Hr1).
    rewrite (eq_abs Hr2).
    
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
    rewrite (eq_abs Hr1) in H'.
    rewrite (eq_abs Hr2) in H'.    
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

      rewrite (eq_abs Hr1).
      rewrite (eq_abs Hr2).
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
  rewrite -subr_eq  in Hq2.
  move/eqP in Hq2.
  rewrite -[LHS]addrA in Hq2.
  have H : q * d - q * d = 0 by rewrite addrC addNr. (* これは補題にしても *)
  rewrite H in Hq2.
  rewrite addr0 in Hq2.
  done.
Qed.

(**
# MathComp での定義
 *)

Print divz.

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


Lemma test1 (n d : nat) :
  (d %| n.+1)%N -> (n %/ d).+1 = (n.+1 %/ d)%N.
Proof.
  move=> H.
Admitted.

Lemma test2 (n d : nat) :
  ~~(d %| n.+1)%N -> ((n %/ d) = (n.+1 %/ d))%N.
Proof.
  move=> H.
Admitted.

Lemma divz_edivz (m d : int) : divz m d = edivz m d.
Proof.
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


Definition divz_d_K_n_absd (m d : int) :=
  let: (K, n) := match m with Posz n => (Posz, n) | Negz n => (Negz, n) end in
  (d, K, n, `|d|).


(*
(*                                                  d  K      n |d| *)
Compute divz_d_K_n_absd p10 p3.             (*      3, Posz, 10, 3 *)
Compute divz_d_K_n_absd p10 m3.             (* Negz 2, Posz, 10, 3 *)
Compute divz_d_K_n_absd m10 p3.             (*      3, Negz,  9, 3 *)
Compute divz_d_K_n_absd m10 m3.             (* Negz 2, Negz,  9, 3 *)

Compute divz            p10 p3.             (* Posz 3 *)
Compute divz            p10 m3.             (* Negz 2 = -3 *)
Compute divz            m10 p3.             (* Negz 3 = -4 *)
Compute divz            m10 m3.             (* Posz 4 *)     

Compute (sgz (Posz 3)) * Posz (10 %/ 3).    (* Posz 3 *)
Compute (sgz (Negz 2)) * Posz (10 %/ 3).    (* Negz 2 = -3 *)
Compute (sgz (Posz 3)) * Negz ( 9 %/ 3).    (* Negz 3 = -4 *)
Compute (sgz (Negz 2)) * Negz ( 9 %/ 3).    (* Posz 4 *)

(* -1, 0, 1 を返す。 *)
Compute sgz (Negz 2)%R.                     (* Negz 0 (= -1) *)
Compute sgz (Posz 0)%R.                     (* Posz 0 *)
Compute sgz (Posz 3)%R.                     (* Posz 1 *)

Compute (Posz 1) * Posz (10 %/ 3).          (* Posz 3 *)
Compute (Negz 0) * Posz (10 %/ 3).          (* Negz 2 = -3 *)
Compute (Posz 1) * Negz ( 9 %/ 3).          (* Negz 3 = -4 *)
Compute (Negz 0) * Negz ( 9 %/ 3).          (* Posz 4 *)

Compute (Posz 1) * Posz 3.                  (* Posz 3 *)
Compute (Negz 0) * Posz 3.                  (* Negz 2 = -3 *)
Compute (Posz 1) * Negz 3.                  (* Negz 3 = -4 *)
Compute (Negz 0) * Negz 3.                  (* Posz 4 *)

(* Definition sgz x : int := if x == 0 then 0 else if x < 0 then -1 else 1. *)
Definition divz (m d : int) :=
  let: (K, n) := match m with Posz n => (Posz, n) | Negz n => (Negz, n) end in
  sgz d * K (n %/ `|d|)%N.
Definition modz (m d : int) : int := m - divz m d * d.

Compute divz            p10 p3.             (* Posz 3 *)
Compute divz            p10 m3.             (* Negz 2 = -3 *)
Compute divz            m10 p3.             (* Negz 3 = -4 *)
Compute divz            m10 m3.             (* Posz 4 *)     

Compute modz            p10 p3.             (* Posz 1 *)
Compute modz            p10 m3.             (* Posz 1 *)
Compute modz            m10 p3.             (* Posz 2 *)
Compute modz            m10 m3.             (* Posz 2 *)

(*
  m  =   q  *   d  + r
  10 =   3  *   3  + 1
  10 = (-3) * (-3) + 1
- 10 = (-4) *   3  + 2
- 10 =   4  * (-3) + 2
 *)

Definition divz' (m d : int) :=
  if (m >= 0) then
    sgz d * sgz m * (`|m| %/ `|d|)%N        (* floor *)
  else
    sgz d * sgz m *
    (if (`|d| %| `|m|)%N then (`|m| %/ `|d|)%N else (`|m| %/ `|d| + 1)%N). (* ceil *)
                                          
Check divz'.
Compute divz'           p10 p3.             (* Posz 3 *)
Compute divz'           p10 m3.             (* Negz 2 = -3 *)
Compute divz'           m10 p3.             (* Negz 3 = -4 *)
Compute divz'           m10 m3.             (* Posz 4 *)     


Definition p9 : int := 9.
Definition p8 : int := 8.   
Definition p7 : int := 7.
Definition p6 : int := 6.
Definition p5 : int := 5.    
Definition p4 : int := 4.
Definition p2 : int := 2.    
Definition p1 : int := 1.    

Definition m9 : int := - 9%:Z.
Definition m8 : int := - 8%:Z.
Definition m7 : int := - 7%:Z.
Definition m6 : int := - 6%:Z.
Definition m5 : int := - 5%:Z.
Definition m4 : int := - 4%:Z.
Definition m2 : int := - 2%:Z.
Definition m1 : int := - 1%:Z.


Compute divz' p9 p3.                        
Compute divz' p8 p3.                        
Compute divz' p7 p3.
Compute divz' p6 p3.
Compute divz' p5 p3.                        
Compute divz' p4 p3.
Compute divz' p3 p3.
Compute divz' p2 p3.                        

Compute divz' p9 m3.                        (* -3 *)
Compute divz' p8 m3.                        (* -2 *)
Compute divz' p7 m3.                        (* -2 *)
Compute divz' p6 m3.                        (* -2 *)
Compute divz' p5 m3.                        (* -1 *)
Compute divz' p4 m3.                        (* -1 *)
Compute divz' p3 m3.                        (* -1 *)
Compute divz' p2 m3.                        (* 0 *)

Compute divz' m9 p3.                        (* -3 *)
Compute divz' m8 p3.                        
Compute divz' m7 p3.
Compute divz' m6 p3.
Compute divz' m5 p3.                        (* -2 *)
Compute divz' m4 p3.
Compute divz' m3 p3.
Compute divz' m2 p3.                        (* -1 *)
Compute divz' m1 p3.                        (* -1 *)

Compute divz' m9 m3.                        (* -9 = 3 * -3  *)
Compute divz' m8 m3.                        (* -8 = 3 * -3 + 1 *)
Compute divz' m7 m3.
Compute divz' m6 m3.
Compute divz' m5 m3.                        (* -5 = 2 * -3 + 1 *)
Compute divz' m4 m3.
Compute divz' m3 m3.
Compute divz' m2 m3.                        (* -2 = 1 * -3 + 1 *)
*)

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

(* END *)
