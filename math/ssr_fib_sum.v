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
補題を含む MathComp の big.v ライブラリ（文献[2][3]）を使って証明してみましょう。

このファイルは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_fib_sum.v


また、

https://github.com/suharahiromichi/coq/blob/master/common/ssromega.v


も必要です。
 *)

Section Fib_1.

(**
# fibonacci 関数の定義
*)
  Fixpoint fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.
 
(**
# 簡単な補題
*)
  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.

  Lemma fib2_ge_1 n : 1 <= fib n.+2.
  Proof.
    elim: n => // n IHn.
    rewrite fib_n.
    rewrite addn_gt0.
      by apply/orP/or_intror.
  Qed.

(**
# Σの補題

bigop.v は、モノイド則の成り立つ演算子に対して、繰返し演算を提供するものです
自然数の加算 addn に対応するのが ``Σ`` ですが、
補題は繰返し演算の一般で示されているので、必要なもを探すのが大変です。

今回は、もっぱら``Σ``を通して bigop.v に慣れることを目標にしますから、
煩瑣になりますが、``Σ``についてだけの補題を証明して置きます。
慣れたならば、直接 bigop.v の補題を使うほうがよいかもしれません。

なお、補題において ``f(i)`` は任意の数列の項を示します（フィボナッチ数列に
限定しません）。
 *)
  
(**
## 0を取り出す。

$$ \sum_{φ}f(i) = 0 $$
 *)
  Lemma sum_nil f :
    \sum_(0 <= i < 0)(f i) = 0.
  Proof.
      by rewrite big_nil.
  Qed.
  
(**
## f(0)項を取り出す。

$$ \sum_{i=0}^{0}f(i) = f(0) $$
 *)
  Lemma sum_f0 f :
    \sum_(0 <= i < 1)(f i) = f 0.
  Proof.
      by rewrite big_cons big_nil addn0.
  Qed.
  
(**
## 最後の1項を取り出す。

$$ \sum_{i=m}^{n}f(i) = \sum_{i=m}^{n-1}f(i) + f(n) $$
 *)
  Lemma sum_last m n f :
    m <= n ->
    \sum_(m <= i < n.+1)(f i) = \sum_(m <= i < n)(f i) + f n.
  Proof.
    move=> Hmn.
      by rewrite big_nat_recr.
  Qed.

(**
# フィボナッチ数列の性質
*)

(**
## 性質1（フィボナッチ数列の和）

$$ \sum_{i=0}^{n}F_i = F_{n+2} - 1 $$

ここでは、帰納法で解く。
 *)
  Lemma lemma1' (n : nat) :
    \sum_(0 <= i < n.+1)(fib i) = fib n.+2 - 1.
  Proof.  
    elim: n => [| n IHn].
    - by rewrite sum_f0.
    - rewrite sum_last; last done.
      rewrite IHn.
      rewrite addnBAC; last by rewrite fib2_ge_1.
      congr (_ - _).
        by rewrite addnC.
  Qed.

(**
## 性質2（積の和）

$$ \sum_{i=0}^{n}(F_i F_1) = F_{n} F_{n+1} $$

*)
  Lemma lemma2 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i * fib i) = fib n * fib n.+1.
  Proof.
    elim: n => [| n IHn].
    - by rewrite sum_f0.
    - rewrite sum_last; last done.
      rewrite IHn.
      rewrite -mulnDl.
      rewrite mulnC.
        by congr (_ * _).
  Qed.

(**
## 性質3 (奇数の和）

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
## 性質4（偶数の和）

$$ \sum_{i=0}^{n}F_{2 i} + 1 = F_{2n+1} $$

*)
  Lemma lemma4 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i.*2) + 1 = fib n.*2.+1.
  Proof.
    elim: n => [| n IHn].
    - by rewrite sum_f0.
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
## 性質5（となり同士のフィボナッチ数列は互いに素である。）
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
