(**
フィボナッチ数列の和
========================

@suharahiromichi

2020/07/01


2020/07/02 構成をみなおした。


2020/07/03 総和を0からにした。
*)

From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

フィボナッチ ffibonacci 数列の和はいくつかのおもしろい性質があります（文献[1]）。
どれも、中学の数学で証明できるものですが、
ここでは、``Σ``の定義と関連する
補題を含む MathComp の bigop.v ライブラリ（文献[3][4]）を使って証明してみましょう。

扱う数は、0以上の整数だけとします。

このファイルは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_fib_sum.v


また、

https://github.com/suharahiromichi/coq/blob/master/common/ssromega.v


も必要です。
 *)

(**
# Σの補題

bigop.v は、モノイド則の成り立つ演算子と単位元に対して、繰返し演算を提供するものです。
自然数の加算 addn と 0 に対応するのが ``Σ`` (``sum``) ですが、
補題は繰返し演算(``big``)の一般で示されているので、必要なもを探すのが大変です。

今回は、もっぱら``Σ``を通して bigop.v に慣れることを目標にしますから、
煩瑣になりますが、``Σ``についてだけの補題を証明して置きます。
慣れたならば、直接 bigop.v の補題を使うほうがよいかもしれません。

なお、本節において $a_n$ は任意の数列の項を示します（フィボナッチ数列に
限定しません）。
 *)

Section Summation.
(**
## 総和の結合と分配

高校で習う、総和についての公式です。

総和の範囲は、$m \lt n$ としてmからnとします。
$m \ge n$ の場合は、Σの中身が単位元となり成立しません。

```math

\sum_{i=m}^{n-1}a_i + \sum_{i=m}^{n-1}b_i = \sum_{i=m}^{n-1}(a_i + b_i) \\

\sum_{i=m}^{n-1}c a_i = c \sum_{i=m}^{n-1}a_i \\

\sum_{i=m}^{n-1}(a_i c) = (\sum_{i=m}^{n-1}a_i) c \\

```
*)
  Lemma sum_split m n a b :
    m < n ->
    \sum_(m <= i < n)(a i) + \sum_(m <= i < n)(b i) = \sum_(m <= i < n)(a i + b i).
  Proof. by rewrite big_split. Qed.

  Lemma sum_distrr m n c a :
    m < n ->
    \sum_(m <= i < n)(c * (a i)) = c * (\sum_(m <= i < n)(a i)).
  Proof. by rewrite big_distrr. Qed.

  Lemma sum_distrl m n a c :
    m < n ->
    \sum_(m <= i < n)((a i) * c) = (\sum_(m <= i < n)(a i)) * c.
  Proof. by rewrite big_distrl. Qed.

(**
## 0を取り出す。

$$ \sum_{i \in \emptyset}a_i = 0 $$

総和をとる範囲が無い場合（0以上0未満）は、単位元``0``になります。
 *)
  Lemma sum_nil' a : \sum_(0 <= i < 0)(a i) = 0.
  Proof.
    by rewrite big_nil.
  Qed.
  
(**
上記の補題は、1以上1未満などの場合にも適用できてしまいますが、任意のmとnで証明しておきます。
*)
  Lemma sum_nil m n a : n <= m -> \sum_(m <= i < n)(a i) = 0.
  Proof.
    move=> Hmn.
    have H : \sum_(m <= i < n)(a i) = \sum_(i <- [::])(a i).
    - apply: congr_big => //=.
      rewrite /index_iota.
      have -> : n - m = 0 by ssromega. (* apply/eqP; rewrite subn_eq0. *)
      done.
    - rewrite H.
      by rewrite big_nil.
  Qed.
  
(**
## ``a n``項を取り出す。

$$ \sum_{i=n}^{n}a_i = a_n $$

総和をとる範囲がひとつの項の場合（n以上n以下）は、``a n`` となります。
 *)
  Lemma sum_nat1 n a :
    \sum_(n <= i < n.+1)(a i) = a n.
  Proof. by rewrite big_nat1. Qed.
  
(**
## 総和の範囲を0起源に振りなおす。

項のインデックスを調整して（ずらして）、mからn+mまでの総和の範囲を0からnまでにします。

$$ \sum_{i=m}^{n+m-1}a_i = \sum_{i=0}^{n-1}a_{i+m} $$
 *)
  Lemma sum_addn (m n : nat) a :
    \sum_(m <= i < n + m)(a i) = \sum_(0 <= i < n)(a (i + m)).
  Proof.
    rewrite -{1}[m]add0n.
    rewrite big_addn.
    have -> : n + m - m = n by ssromega.
    done.
  Qed.

(**
これは、任意のmで成り立ちますが、``Σ``の中の項のインデックスの``i.+1``を
``i + 1`` に書き換えられないため、``i.+1`` と ``i.+2`` の場合については、
個別に用意する必要があります。実際はこちらの方を使います。
*)
  Lemma sum_add1 n a :
    \sum_(1 <= i < n.+1)(a i) = \sum_(0 <= i < n)(a i.+1).
  Proof. by rewrite big_add1 succnK. Qed.

  Lemma sum_add2 n a :
    \sum_(2 <= i < n.+2)(a i) = \sum_(0 <= i < n)(a i.+2).
  Proof. by rewrite 2!big_add1 2!succnK. Qed.
  
(**
## 最初の項をΣの外に出す。

$$ \sum_{i=m}^{n-1}a_i = a_m + \sum_{i=m+1}^{n-1}a_i $$
 *)
  Lemma sum_first m n a :
    m < n ->
    \sum_(m <= i < n)(a i) = a m + \sum_(m.+1 <= i < n)(a i).
  Proof.
    move=> Hn.
    by rewrite big_ltn.
  Qed.

(**
総和の範囲の起点を変えずに、インデックスをずらす補題もあります。

$$ \sum_{i=m}^{n}a_i = a_m + \sum_{i=m}^{n-1}a_{i + 1} $$
*)
  Lemma sum_first' m n a :
    m <= n ->
    \sum_(m <= i < n.+1)(a i) = a m + \sum_(m <= i < n)(a i.+1).
  Proof.
    move=> Hn.
    by rewrite big_nat_recl.
  Qed.
  
(**
## 最後の項をΣの外に出す。

$$ \sum_{i=m}^{n}a_i = \sum_{i=m}^{n-1}a_i + a_n $$
 *)
  Lemma sum_last m n a :
    m <= n ->
    \sum_(m <= i < n.+1)(a i) = \sum_(m <= i < n)(a i) + a n.
  Proof.
    move=> Hmn.
    by rewrite big_nat_recr.
  Qed.
End Summation.  

Section Fib_1.
(**
# フィボナッチ fibonacci 数列の定義

フィボナッチ数列 $ a_n $ を index についての関数として定義します。

```math

\begin{eqnarray}
F_0 &=& 0 \\
F_1 &=& 1 \\
F_n &=& F_{n - 2} + F_{n - 1} \\
\end{eqnarray}

```

フィボナッチ数列の定義そのままなので、再帰関数になります。

*)
  Fixpoint fib n : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as n).+1 => fib m + fib n (* fib n.-2 + fib n.-1 *)
    end.
 
(**
# 簡単な補題

定義から導かれる補題を証明しておきます。
*)
  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof. done. Qed.

  Lemma fibn1_ge_1 n : 1 <= fib n.+1.
  Proof.
    elim: n => // n IHn.
    rewrite fib_n.
    rewrite addn_gt0.
    by apply/orP/or_intror.
  Qed.
  
  Lemma fibn2_ge_1 n : 1 <= fib n.+2.
  Proof.
    elim: n => // n IHn.
    rewrite fib_n.
    rewrite addn_gt0.
    by apply/orP/or_intror.
  Qed.
  
(**
# フィボナッチ数列の性質

定理は、概ね文献[2]にそいます。n は $ 0 \le n $ の自然数として、
総和の範囲は 0 から n とします（$ \sum_{i=0}^{n}a_i $）。
MathCompでは ``\sum_(0 <= i < n.+1)(a i)`` となります。

$F_0 = 0$なので、1からの総和でも結果に変わりがないのですが（奇数の和をのぞく）、
nに対する数学的帰納法を使うときなどで、$n=0$の
場合に、$\sum_{i=0}^{0}a_i = a_0$ であるようにすると気持ちがよいからです。

1からの場合は、(1から0の)空の総和となり、$\sum_{i=1}^{0}a_i = 0$ 
と単位元になってしまいます（それでも、成立する場合があります）。
*)

(**
## 性質0 (数列の和の加算)

$$ \sum_{i=0}^{n}F_i + \sum_{i=0}^{n}F_{i+1} = \sum_{i=0}^{n}F_{i+2} $$
*)
  Lemma add_of_sum_of_seq_of_fib n :
    \sum_(0 <= i < n.+1)(fib i) + \sum_(0 <= i < n.+1)(fib i.+1) =
    \sum_(0 <= i < n.+1)(fib i.+2).
  Proof. by rewrite sum_split. Qed.
  
(**
## 性質1 (フィボナッチ数列の和)

$$ \sum_{i=0}^{n}F_i = F_{n+2} - 1 $$
 *)
  Lemma sum_of_seq_of_fib n :
    \sum_(0 <= i < n.+1)(fib i) = fib n.+2 - 1.
  Proof.  
    have H := add_of_sum_of_seq_of_fib n.
    rewrite -sum_add1 -sum_add2 in H.
    rewrite [\sum_(1 <= i < n.+2)(fib i)]sum_first in H; last done.
    rewrite [\sum_(2 <= i < n.+3)(fib i)]sum_last in H; last done.
    rewrite addnA in H.
    rewrite [\sum_(2 <= i < n.+2) fib i + fib n.+2]addnC in H.
    
    (* 前提 H の両辺の共通項を消す。 *)
    move/eqP in H.
    rewrite eqn_add2r in H.
    move/eqP in H.

    rewrite -H.
    rewrite [fib 1]/=.
      by ssromega.                   (* rewrite addn1 subn1 succnK. *)
  Qed.
  
(**
別証明として、n についての数学的帰納法で解いてみます。

こちらのほうが随分簡単そうなので、
以降の性質も帰納法で証明してみます。
 *)
  Lemma sum_of_seq_of_fib' n :
    \sum_(0 <= i < n.+1)(fib i) = fib n.+2 - 1.
  Proof.  
    elim: n => [| n IHn].
    - by rewrite sum_nat1.
    - rewrite sum_last; last done.
      rewrite IHn.
      rewrite addnBAC; last by rewrite fibn2_ge_1.
      congr (_ - _).
      by rewrite addnC.
  Qed.

(**
## 性質2 (二乗の和)

$$ \sum_{i=0}^{n}(F_i)^2 = F_{n} F_{n + 1} $$

*)
  Lemma sum_of_seq_of_sqr_of_fib n :
    \sum_(0 <= i < n.+1)((fib i)^2) = fib n * fib n.+1.
  Proof.
    elim: n => [| n IHn].
    - by rewrite sum_nat1.
    - rewrite sum_last; last done.
      rewrite IHn.
      rewrite -mulnDl.
      rewrite mulnC.
      by congr (_ * _).
  Qed.

(**
## 性質3 (奇数の和)

これは、0からの総和と、1からの総和で結果が異なるので、両方証明しておきます。

```math

\sum_{i=0}^{n-1}F_{2 i + 1} = F_{2n} \\

\sum_{i=1}^{n}F_{2 i - 1} = F_{2n}
```

*)  
  Lemma sum_of_seq_of_odd_index_of_fib n :
    \sum_(0 <= i < n)(fib i.*2.+1) = fib n.*2.
    elim: n => [| n IHn].
    - by rewrite sum_nil.
    - have -> : n.+1.*2 = n.*2.+2
        by rewrite -addn1 -!muln2; ssromega.
      rewrite fib_n.                        (* 右辺 *)
      rewrite sum_last; last done.          (* 左辺 *)
      rewrite IHn.
      by congr (_ + _).
  Qed.

  Lemma sum_of_seq_of_odd_index_of_fib' n :
    \sum_(1 <= i < n.+1)(fib i.*2.-1) = fib n.*2.
  Proof.
    elim: n => [| n IHn].
    - by rewrite sum_nil.
    - have -> : n.+1.*2 = n.*2.+2
        by rewrite -addn1 -!muln2; ssromega.
      rewrite fib_n.                        (* 右辺 *)
      rewrite sum_last; last done.          (* 左辺 *)
      rewrite IHn.
      by congr (_ + _).
  Qed.
  
(**
## 性質4 (偶数の和)

$$ \sum_{i=0}^{n}F_{2 i} = F_{2 n + 1} - 1 $$

*)
  Lemma l_sum_of_seq_of_even_index_of_fib n :
    \sum_(0 <= i < n.+1)(fib i.*2) + 1 = fib n.*2.+1.
  Proof.
    elim: n => [| n IHn].
    - by rewrite sum_nat1.
    - have H : n.+1.*2 = n.*2.+2
        by rewrite doubleS; ssromega.
      (* rewrite -addn1 -!muln2 addn1 2!muln2 doubleS. *)
      
      (* 右辺 *)
      rewrite H !fib_n -{1}IHn -addnA -fib_n.
      rewrite [1 + fib n.*2.+2]addnC.
      
      (* 左辺 *)      
      rewrite sum_last; last done.
      rewrite -H -addnA.
      done.
  Qed.
  
  Lemma sum_of_seq_of_even_index_of_fib n :
    \sum_(0 <= i < n.+1)(fib i.*2) = fib n.*2.+1 - 1.
  Proof.
    rewrite -l_sum_of_seq_of_even_index_of_fib.
    by rewrite addn1 subn1 -pred_Sn.
  Qed.
  
(**
# おまけ

## 性質5 (となりどうしのフィボナッチ数列は互いに素である)
 *)
  Lemma coprime_cons_fibs n : coprime (fib n) (fib n.+1).
  Proof.
    rewrite /coprime.
    elim: n => [//= | n IHn].
    rewrite fib_n.
    by rewrite gcdnDr gcdnC.
  Qed.
End Fib_1.

(**
# 文献

[1] フィボナッチ数列と中学入試問題

http://www.suguru.jp/Fibonacci/


[2] ProofWiki
- https://proofwiki.org/wiki/Sum_of_Sequence_of_Fibonacci_Numbers
- https://proofwiki.org/wiki/Sum_of_Sequence_of_Squares_of_Fibonacci_Numbers
- https://proofwiki.org/wiki/Sum_of_Sequence_of_Odd_Index_Fibonacci_Numbers
- https://proofwiki.org/wiki/Sum_of_Sequence_of_Even_Index_Fibonacci_Numbers
- https://proofwiki.org/wiki/Consecutive_Fibonacci_Numbers_are_Coprime


[3] 萩原学 アフェルト・レナルド、「Coq/SSReflect/MathCompによる定理証明」、森北出版


[4] Reynald Affeldt, cheat sheet bigop.v

https://staff.aist.go.jp/reynald.affeldt/ssrcoq/bigop_doc.pdf
*)

(* END *)
