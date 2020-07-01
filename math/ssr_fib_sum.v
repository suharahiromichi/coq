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

定義から導かれる補題を証明しておきます。
*)
  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.

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
## インデックスを0起源に振りなおす（reindexする)。

項の中のインデックスの足し算を調整して、mからn+mまでのインデックスを
0からnまでに振り直します。

$$ \sum_{i=m}^{n+m}f(i) = \sum_{i=0}^{n}f(i+m) $$
 *)
  Lemma l_reindex (m n : nat) f :
    \sum_(m <= i < n + m)(f i) = \sum_(0 <= i < n)(f (i + m)).
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
  Lemma l_reindex_1 (n : nat) f :
    \sum_(1 <= i < n.+1)(f i) = \sum_(0 <= i < n)(f i.+1).
  Proof.
      by rewrite big_add1 succnK.
  Qed.

  Lemma l_reindex_2 (n : nat) f :
    \sum_(2 <= i < n.+2)(f i) = \sum_(0 <= i < n)(f i.+2).
  Proof.
      by rewrite 2!big_add1 2!succnK.
  Qed.
  

(**
### 最初の1項を取り出す。

$$ \sum_{i=m}^{n-1}f(i) = f(m) + \sum_{i=m+1}^{n-1}f(i)  $$
 *)
  Lemma sum_first m n f :
    m < n ->
    \sum_(m <= i < n)(f i) = f m + \sum_(m.+1 <= i < n)(f i).
  Proof.
    move=> Hn.
      by rewrite big_ltn.
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
## split

$$ \forall i, f(i) + g(i) = h(i) \to
\sum_{i=0}^{n}f(i) + \sum_{i=0}^{n}g(i) = \sum_{i=0}^{n}h(i) $$
*)
  Lemma sum_split n f g :
    \sum_(0 <= i < n)(f i) + \sum_(0 <= i < n)(g i) =
    \sum_(0 <= i < n)(f i + g i).
  Proof.
      by rewrite big_split.
  Qed.
  
(**
# フィボナッチ数列の性質
*)

(**
## 性質0 (数列の和の加算)

$$ \sum_{i=0}^{n}F_i + \sum_{i=0}^{n}F_{i+1} = \sum_{i=0}^{n}F_{i+2} $$

*)
  Lemma l_sum_of_seq (n : nat) :
    \sum_(0 <= i < n)(fib i) + \sum_(0 <= i < n)(fib i.+1) =
    \sum_(0 <= i < n)(fib i.+2).
  Proof.
      by rewrite sum_split.
  Qed.
  
(**
## 性質1（フィボナッチ数列の和）

$$ \sum_{i=0}^{n}F_i = F_{n+2} - 1 $$

 *)
  Lemma lemma1 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i) = fib n.+2 - 1.
  Proof.  
    have H := l_sum_of_seq n.+1.
    rewrite -l_reindex_1 -l_reindex_2 in H.
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
    - by rewrite sum_f0.
    - rewrite sum_last; last done.
      rewrite IHn.
      rewrite addnBAC; last by rewrite fibn2_ge_1.
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
# 使わなかった補題 (削除する)
*)

Section Backup.

  Lemma l1_sub2 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i) = \sum_(0 <= i < n)(fib i.+1).
  Proof.
    have H : 0 <= n by rewrite leq0n.
    Check (big_nat_recl n 0 _ H).
    rewrite big_nat_recl; last done.
      by rewrite add0n.
  Qed.
  
  Lemma l1_sub3 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i.+1) = 1 + \sum_(0 <= i < n)(fib i.+2).
  Proof.
    have H : 0 <= n.+1 by rewrite leq0n.
    Check (big_nat_recl n 0 _ H).
    rewrite big_nat_recl; last done.
      by rewrite [fib 1]/=.
  Qed.
  
  Lemma test1 : fib 1 = \sum_(0 <= i < 1)(fib i.+1).
  Proof.
    rewrite big_cons.
    rewrite big_nil.
    done.
  Qed.
  
  Lemma l1_sub2' (n : nat) :
    1 <= n -> \sum_(1 <= i < n.+1)(fib i) = fib 1 + \sum_(1 <= i < n)(fib i.+1).
  Proof.
    move=> H.
    rewrite -big_nat_recl; last done.
    done.
  Qed.

  Lemma test2 : fib 1 = \sum_(0 <= i < 1)(fib i.+1).
  Proof.
      by rewrite big_cons big_nil.
  Qed.
  
  Lemma test0 : \sum_(0 <= i < 1)(fib i) = 0.
  Proof.
      by rewrite big_cons big_nil.
  Qed.
  
  Lemma cat_iota (n : nat) : 1 <= n -> index_iota 0 1 ++ index_iota 1 n = index_iota 0 n.
  Proof.
    move=> Hn.
    rewrite /index_iota.
    rewrite -iota_add.
    rewrite !subn0.
    rewrite subnKC //=.
  Qed.

  Lemma test4 (n : nat) :
    1 <= n ->
    \sum_(0 <= i < 1)(fib i) + \sum_(1 <= i < n)(fib i) =
    \sum_(0 <= i < n)(fib i).
  Proof.
    move=> Hn.
    rewrite -big_cat.
    rewrite cat_iota; last done.
    done.
    
    (* sum_first を使えばよい。 *)
    Restart.
    move=> Hn.
    rewrite [\sum_(0 <= i < n) fib i]sum_first; last done.
    by rewrite big_cons big_nil.
  Qed.

(**
## コンギュランス
*)
  Lemma eq_add m n k : (m + k = n + k) <-> (m = n).
  Proof.
    split=> H.
    - apply/eqP.
      rewrite -(eqn_add2r k).
        by apply/eqP.
    - by rewrite H.
  Qed.
  
End Backup.


(**
# 文献

[1] フィボナッチ数列と中学入試問題

http://www.suguru.jp/Fibonacci/


[2] 萩原学 アフェルト・レナルド、「Coq/SSReflect/MathCompによる定理証明」、森北出版


[3] Reynald Affeldt, cheat sheet bigop.v

https://staff.aist.go.jp/reynald.affeldt/ssrcoq/bigop_doc.pdf
*)

(* END *)
