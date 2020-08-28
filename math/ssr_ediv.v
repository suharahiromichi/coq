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
たとえば教科書に記載されるのは、

$$ 0 \le r \lt | d | $$

にように、剰余を0または正の範囲に制限することです。
これは、プログラミング言語Pascalの ``mod`` 演算で採用されています。
また Coq/MathComp の ``%%`` もこの定義です。

これを満たす d と r を求めるには、次のふたつの方法がありますが、
ここでは、絶対値の割算を使う方法を採用します。

- ``m / d`` を実数で求め、切り捨てて、qとする。
- ``|m| / |d|`` と絶対値で求め、mが正なら切り捨て、mが負なら切り上げ(注1)し、
符号を復元して(注2)、qとする。

(注1) 自然数の割算における切り捨てと切り上げは後で定義します。

(注2) m と d と q の符号は、奇数個の関係にあります。


ここでは、

- r が 0 以上の制限を加えると、qとrが一意に決まることを証明する。
- q と r を求める式を具体的に定義して、r が0以上であることを証明する。

これによって、整数割算の健全性を示すことができるはずです。
証明には Coq/MathComp を使います。

最後に、ここで示した以外の整除法について言及します。

このファイルは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_ediv.v

証明スクリプトは模範回答ではなく、一例として参考程度にしてください。
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import ssromega.                    (* ssromega タクティク *)
Require Import Recdef.                      (* Function コマンド *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)

Definition p10 : int := 10.                 (* Posz 10 *)
Definition m10 : int := - 10%:Z.            (* Negz 2 *)
Definition p3 : int := 3.                   (* Posz 3 *)
Definition m3 : int := - 3%:Z.              (* Negz 2 *)

Lemma lt_le (x y : int) : x < y -> x <= y.
Proof.
  move=> H.
  Search _ (_ <= _).
  rewrite ler_eqVlt.
    by apply/orP/or_intror.
Qed.

Lemma eq_le (x y : int) : x = y -> x <= y.
Proof.
  move=> H.
  Search _ (_ <= _).
  rewrite ler_eqVlt.
  apply/orP/or_introl.
    by apply/eqP.
Qed.

(**
# ユーグリッド除法の定義
*)
Definition divz_floor (m d : int) : int := (`|m| %/ `|d|)%Z.
Compute divz_floor p10 p3.                  (* 3 *)

Definition divz_ceil (m d : int) : int :=
  if (d %| m)%Z then (`|m| %/ `|d|)%Z else ((`|m| %/ `|d|)%Z + 1).
Check divz_ceil : int -> int -> int.
Compute divz_ceil p3 p3.                    (* 1 *)
Compute divz_ceil p10 p3.                   (* 4 *)
Compute divz_ceil p10 m3.                   (* 4 *)
Compute divz_ceil m10 p3.                   (* 4 *)
Compute divz_ceil m10 m3.                   (* 4 *)

Lemma divz_floorp (m d : int) : d != 0 -> (divz_floor m d) * `|d| <= `|m|.
Proof.
  move=> Hd.
  rewrite /divz_floor.
  apply: lez_floor.
  move/normr0P in Hd.
    by apply/eqP.
Qed.

Check lez_floor
  : forall (m : int) (d : int_ZmodType), d != 0 -> (m %/ d)%Z * d <= m.
Check ltz_ceil
  : forall m d : int_numDomainType, 0 < d -> m < ((m %/ d)%Z + 1) * d.

Lemma leq_equal m d : d != 0 -> (d %| m)%Z -> (m %/ d)%Z * d = m.
Proof.
  move=> Hd Hdm.
  apply/eqP.
  Check dvdz_eq
    : forall d m : int, (d %| m)%Z = ((m %/ d)%Z * d == m).
  rewrite -dvdz_eq.
  done.
Qed.

Lemma divz_ceilp (m d : int) : d != 0 -> `|m| <= (divz_ceil m d) * `|d|.
Proof.
  move=> Hd.
  rewrite /divz_ceil.
  case: ifP => Hdm.
  - apply: eq_le.
    rewrite leq_equal.
    + done.
    + by rewrite normr_eq0.
    + Search _ ( (_  %| _)%Z ).
        by rewrite dvdzE in Hdm.
  - apply: lt_le.
    apply: ltz_ceil.
      by rewrite normr_gt0.
Qed.

Definition edivz (m d : int) : int :=
  if (0 <= m) then
    sgz d * divz_floor m d
  else
    - sgz d * divz_ceil m d.

Definition emodz (m d : int) : int :=
  m - (edivz m d) * d.

Compute edivz p10 p3.                       (* 3 *)
Compute edivz p10 m3.                       (* -3 *)
Compute edivz m10 p3.                       (* -4 *)
Compute edivz m10 m3.                       (* 4 *)

Compute emodz p10 p3.                       (* 1 *)
Compute emodz p10 m3.                       (* 1 *)
Compute emodz m10 p3.                       (* 2 *)
Compute emodz m10 m3.                       (* 2 *)

(**
# 剰余が正であることの証明
*)
Lemma nge0_lt0 (m : int) : (0 <= m) = false -> m < 0.
Proof.
  move=> H.
  move/negbT in H.
  Search _ (~~ (_ <= _)).
  by rewrite -ltrNge in H.
Qed.

Lemma ltz_m_abs (m : int) : m < 0 -> m = - `|m|.
Proof.
  move=> H.
  rewrite ltr0_norm //=.
    by rewrite opprK.                            (* oppz ではない。 *)
Qed.

Lemma ediv_mod_ge0 (m d : int) : d != 0 -> 0 <= emodz m d.
Proof.
  move=> Hd.
  rewrite /emodz /edivz.
  case: ifP => H.
  - rewrite -mulrAC.
    Check abszEsg : forall m : int, `|m|%Z = sgz m * m.
    rewrite -abszEsg mulrC.
    rewrite subr_ge0.                       (* ssrnum *)
    Check normr_idP.
    move/normr_idP in H.
    rewrite -{2}H.
      (* (`|m| %/ `|d|)%Z * `|d|%N <= `|m| *)
      by apply: divz_floorp.

  (* m + - (- sgz d) * divz_ceil m d * d *)
  (* m + - - (sgz d * divz_ceil m d * d) *)      
  - rewrite !mulNr.
    rewrite [- - (sgz d * divz_ceil m d * d)]oppzK.
    rewrite -mulrAC.
    rewrite -abszEsg mulrC.
    move/nge0_lt0 in H.
    rewrite {1}(ltz_m_abs H).
    rewrite addrC subr_ge0.               (* addzC でない！ *)
      by apply: divz_ceilp.
Qed.

(**
# 一意性の証明
*)

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

Lemma lemma1 (q d : nat) : (q * d < d)%N -> (q = 0)%N.
Proof.
  rewrite -{2}[d]mul1n.
  Check ltn_mul2r
    : forall m n1 n2 : nat, (n1 * m < n2 * m)%N = (0 < m)%N && (n1 < n2)%N.
  rewrite ltn_mul2r.
  move/andP => [Hd Hq].
    by ssromega.
Qed.

Lemma eq_eqabsabs (x y : int) : x = y -> (`|x| = `|y|).
Proof.
    by move=> ->.
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

Lemma eq_abs (x : int) : 0 <= x -> x = `|x|.
Proof. by move/normr_idP. Qed.


(* 自然数の補題 *)
Lemma eq_subn n : (n - n = 0)%N.
Proof. apply/eqP. by rewrite subn_eq0. Qed.

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
    + move/nge0_lt0 in H'.
      Search _ (_ - _ < 0).
      rewrite subr_lt0 in H'.
      move/lt_le in H'.
      done.

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

Lemma edivz_uniqness (r1 r2 q1 q2 m d : int) :
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

(**
# MathComp での定義
 *)

Definition divz_d_K_n_absd (m d : int) :=
  let: (K, n) := match m with Posz n => (Posz, n) | Negz n => (Negz, n) end in
  (d, K, n, `|d|).


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
