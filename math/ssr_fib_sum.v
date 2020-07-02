(**
フィボナッチ数列の和
========================

@suharahiromichi

2020/07/01
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

フィボナッチ ffibonacci 数列の和はいくつかのおもしろい性質があります（文献[1]）。
どれも、中学の数学で証明できるものですが、
ここでは、``Σ``の定義と関連する
補題を含む MathComp の bigop.v ライブラリ（文献[2][3]）を使って証明してみましょう。

このファイルは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_fib_sum.v


また、

https://github.com/suharahiromichi/coq/blob/master/common/ssromega.v


も必要です。
 *)

(**
# Σの補題

bigop.v は、モノイド則の成り立つ演算子に対して、繰返し演算を提供するものです
自然数の加算 addn に対応するのが ``Σ`` ですが、
補題は繰返し演算の一般で示されているので、必要なもを探すのが大変です。

今回は、もっぱら``Σ``を通して bigop.v に慣れることを目標にしますから、
煩瑣になりますが、``Σ``についてだけの補題を証明して置きます。
慣れたならば、直接 bigop.v の補題を使うほうがよいかもしれません。

なお、本節において ``a n`` は任意の数列の項を示します（フィボナッチ数列に
限定しません）。
 *)

Section Summation.
(**
## 総和の結合と分配

$$ \sum_{i=0}^{n-1}a_i + \sum_{i=0}^{n-1}b_i = \sum_{i=0}^{n-1}(a_i + b_i) $$

$$ \sum_{i=0}^{n-1}(c a_i) = c \sum_{i=0}^{n-1}a_i $$

$$ \sum_{i=0}^{n-1}(a_i c) = \sum_{i=0}^{n-1}a_i c$$

$$ \sum_{i=0}^{n-1}1 = n  1 $$
*)
  Lemma sum_split n a b :
    \sum_(0 <= i < n)(a i) + \sum_(0 <= i < n)(b i) = \sum_(0 <= i < n)(a i + b i).
  Proof. by rewrite big_split. Qed.

  Lemma sum_distrr n c a :
    \sum_(0 <= i < n)(c * (a i)) = c * (\sum_(0 <= i < n)(a i)).
  Proof. by rewrite big_distrr. Qed.

  Lemma sum_distrl n a c :
    \sum_(0 <= i < n)((a i) * c) = (\sum_(0 <= i < n)(a i)) * c.
  Proof. by rewrite big_distrl. Qed.

  Lemma sum_n n : \sum_(0 <= i < n)(1) = n.-1.
  Proof. Admitted.

(**
## 0を取り出す。

$$ \sum_{φ}a_i = 0 $$
 *)
  Lemma sum_nil a :
    \sum_(0 <= i < 0)(a i) = 0.
  Proof.
      by rewrite big_nil.
  Qed.
  
(**
## a_n 項を取り出す。

$$ \sum_{i=n}^{n}a_i = a_n $$
 *)
  Lemma sum_an n a :
    \sum_(n <= i < n.+1)(a i) = a n.
  Proof. by rewrite big_nat1. Qed.
  
(**
## インデックスを0起源に振りなおす（reindexする)。

項の中のインデックスの足し算を調整して、mからn+mまでのインデックスを
0からnまでに振り直します。

$$ \sum_{i=m}^{n+m}a_i = \sum_{i=0}^{n}a_{i+m} $$
 *)
  Lemma reindex (m n : nat) a :
    \sum_(m <= i < n + m)(a i) = \sum_(0 <= i < n)(a (i + m)).
  Proof.
    rewrite -{1}[m]add0n.
    rewrite big_addn.
    have -> : n + m - m = n by ssromega.
    done.
  Qed.

(**
reindex は、任意のmで成り立ちますが、``Σ``の中の項のインデクスの``i.+1``を
``i + 1`` に書き換えられないため、``i.+1`` と ``i.+2`` の場合については、
reindex を個別に用意する必要があります。実際はこちらの方を使います。
*)
  Lemma reindex_1 n a :
    \sum_(1 <= i < n.+1)(a i) = \sum_(0 <= i < n)(a i.+1).
  Proof. by rewrite big_add1 succnK. Qed.

  Lemma reindex_2 n a :
    \sum_(2 <= i < n.+2)(a i) = \sum_(0 <= i < n)(a i.+2).
  Proof. by rewrite 2!big_add1 2!succnK. Qed.
  

(**
### 最初の1項を取り出す。

$$ \sum_{i=m}^{n-1}a_i = a_m + \sum_{i=m+1}^{n-1}a_i  $$
 *)
  Lemma sum_first m n a :
    m < n ->
    \sum_(m <= i < n)(a i) = a m + \sum_(m.+1 <= i < n)(a i).
  Proof.
    move=> Hn.
      by rewrite big_ltn.
  Qed.
  
(**
## 最後の1項を取り出す。

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

フィボナッチ数列 ``a_n`` を再帰関数として定義します。
*)
  Fixpoint fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
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
*)

(**
## 性質0 (数列の和の加算)

$$ \sum_{i=0}^{n-1}F_i + \sum_{i=0}^{n-1}F_{i+1} = \sum_{i=0}^{n-1}F_{i+2} $$

*)
  Lemma sum_of_seq (n : nat) :
    \sum_(0 <= i < n)(fib i) + \sum_(0 <= i < n)(fib i.+1) =
    \sum_(0 <= i < n)(fib i.+2).
  Proof. by rewrite sum_split. Qed.
  
(**
## 性質1 (フィボナッチ数列の和)

$$ \sum_{i=0}^{n}F_i = F_{n+2} - 1 $$

 *)
  Lemma lemma1 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i) = fib n.+2 - 1.
  Proof.  
    have H := sum_of_seq n.+1.
    rewrite -reindex_1 -reindex_2 in H.
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
      by rewrite addn1 subn1 succnK.
  Qed.

(**
別証明として、n についての数学的帰納法で解いてみます。

こちらのほうが随分簡単そうなので、
以降の性質も帰納法で証明してみます。
 *)
  Lemma lemma1' (n : nat) :
    \sum_(0 <= i < n.+1)(fib i) = fib n.+2 - 1.
  Proof.  
    elim: n => [| n IHn].
    - by rewrite sum_an.
    - rewrite sum_last; last done.
      rewrite IHn.
      rewrite addnBAC; last by rewrite fibn2_ge_1.
      congr (_ - _).
        by rewrite addnC.
  Qed.

(**
## 性質2 (積の和)

$$ \sum_{i=0}^{n}(F_i F_1) = F_{n} F_{n+1} $$

*)
  Lemma lemma2 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i * fib i) = fib n * fib n.+1.
  Proof.
    elim: n => [| n IHn].
    - by rewrite sum_an.
    - rewrite sum_last; last done.
      rewrite IHn.
      rewrite -mulnDl.
      rewrite mulnC.
        by congr (_ * _).
  Qed.

(**
## 性質3 (奇数の和)

$$ \sum_{i=0}^{n-1}F_{2 i + 1} = F_{2n} $$

*)  
  Lemma lemma3 (n : nat) :
    \sum_(0 <= i < n)(fib i.*2.+1) = fib n.*2.
  Proof.
    elim: n => [| n IHn].
    - by rewrite sum_nil.
    - have -> : n.+1.*2 = n.*2.+2.
      + rewrite -addn1 -!muln2.
          by ssromega.
      + rewrite fib_n.                      (* 右辺 *)
        rewrite sum_last; last done.        (* 左辺 *)
        rewrite IHn.
          by congr (_ + _).
  Qed.

(**
## 性質4 (偶数の和)

$$ \sum_{i=0}^{n}F_{2 i} + 1 = F_{2n+1} $$

*)
  Lemma lemma4 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i.*2) + 1 = fib n.*2.+1.
  Proof.
    elim: n => [| n IHn].
    - by rewrite sum_an.
    - have H : n.+1.*2 = n.*2.+2
        by rewrite -addn1 -!muln2 addn1 2!muln2 doubleS.
      
      (* 右辺 *)
      rewrite H.
      rewrite !fib_n.
      rewrite -{1}IHn.
      rewrite -addnA.
      rewrite -fib_n.
      rewrite [1 + fib n.*2.+2]addnC.
      
      (* 左辺 *)      
      rewrite sum_last; last done.
      rewrite -H -addnA.
      done.
  Qed.

(**
# おまけ

## 性質5 (となりどうしのフィボナッチ数列は互いに素である)
 *)
  Lemma lemma5 (n : nat) : coprime (fib n) (fib n.+1).
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


[2] 萩原学 アフェルト・レナルド、「Coq/SSReflect/MathCompによる定理証明」、森北出版


[3] Reynald Affeldt, cheat sheet bigop.v

https://staff.aist.go.jp/reynald.affeldt/ssrcoq/bigop_doc.pdf
*)

(* END *)
