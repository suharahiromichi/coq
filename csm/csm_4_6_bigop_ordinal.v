(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.6 bigop.v --- 総和、相乗のライブラリ (ordinal 編)

======

2024_01_08 @suharahiromichi
 *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 総和についての補題（他のbigopでも成り立つ）
 *)
Section Summation2.
(**
## 総和の結合と分配

高校で習う、総和についての公式です。

```math

\sum_{i=0}^{n-1}a_i + \sum_{i=0}^{n-1}b_i = \sum_{i=0}^{n-1}(a_i + b_i) \\

\sum_{i=0}^{n-1}c a_i = c \sum_{i=0}^{n-1}a_i \\

\sum_{i=0}^{n-1}(a_i c) = (\sum_{i=0}^{n-1}a_i) c \\

\sum_{i=0}^{n-1} c = n c \\

```
*)
  Lemma sum_split n a b :
    \sum_(i < n)(a i) + \sum_(i < n)(b i) = \sum_(i < n)(a i + b i).
  Proof. by rewrite big_split. Qed.

  Lemma sum_distrr n c a :
    \sum_(i < n)(c * (a i)) = c * (\sum_(i < n)(a i)).
  Proof. by rewrite big_distrr. Qed.

  Lemma sum_distrl n a c :
    \sum_(i < n)((a i) * c) = (\sum_(i < n)(a i)) * c.
  Proof. by rewrite big_distrl. Qed.

  Lemma sum_cinst n c :
    \sum_(i < n) c = n * c.
  Proof. by rewrite big_const_ord iter_addn_0 mulnC. Qed.
  
(**
# Σの中身の書き換え

Σの中の i は、ローカルに束縛されている（ラムダ変数である）ので、
直接書き換えることはできません。一旦、取り出して書き換えることになります。
 *)
  Lemma eq_sum n a b : a =1 b ->
                       \sum_(i < n)(a i) = \sum_(j < n)(b j).
  Proof.
    move=> Hab.                             (* =1 は第1階の=です。 *)
    by apply: eq_big.
  Qed.
  
(**
# 入れ子（ネスト）
 *)
(**
## ネストの入れ替え（総和どうしの場合）

$$ \sum_{i=0}^{m-1}(\sum_{j=0}^{n-1)} a_{i j} =
   \sum_{j=0}^{n-1}(\sum_{i=0}^{m-1)} a_{i j} $$
*)
  Lemma exchamge_sum m n a :
    \sum_(i < m) (\sum_(j < n) (a i j)) =
    \sum_(j < n) (\sum_(i < m) (a i j)).
  Proof. by rewrite exchange_big. Qed.
  
(**
## ネストの入れ替え（総和と総乗の場合）

$$ \prod_{i=0}^{m-1}(\sum_{j=0}^{n-1)} a_{i j} =
   \sum_{j=0}^{n-1}(\prod_{i=0}^{m-1)} a_{i j} $$
*)
  (* F : 'I_m -> 'I_n -> _ なので、aより前にmとnを定義しないといけない。 *)
  Lemma prod_distr_sum' m n a :
    \prod_(i < m) (\sum_(j < n) (a i j)) =
    \sum_(j < n) (\prod_(i < m) (a i j)).
  Proof. Admitted.
  
  (* 次のかたちでしか、証明できないようだ。 *)
  Lemma prod_distr_sum m n a :
    \prod_(i in 'I_m) (\sum_(j : 'I_n)(a i j)) =
    \sum_(f : {ffun 'I_m -> 'I_n}) (\prod_(i : 'I_m)(a i (f i))).
  Proof. rewrite -bigA_distr_bigA. done. Qed.
  Check bigA_distr_bigA
    : forall (R : Type) (zero one : R) (times : Monoid.mul_law zero)
         (plus : Monoid.add_law zero times) (I J : finType) 
         (F : I -> J -> R),
       \big[times/one]_(i : I) \big[plus/zero]_(j : J) F i j =
       \big[plus/zero]_(f : {ffun I -> J}) \big[times/one]_(i : I) F i (f i).
  
(**
a(i, j) が a(i, f(i)) になっている。

こで、f は、 定義域 {0, 1}、値域 {0, 1, 2} である関数(finfun)のすべて。
全部で 3^2 = 9 個ある。

Π_i=1,2 Σ_j=1,3 aij
= (a00 + a01 + a02)(a10 + a11 + a12)
= a00 a10 + a00 a11 + a00 a12
+ a01 a10 + a01 a11 + a01 a12
+ a02 a10 + a02 a11 + a02 a12
= Σ_f a0(f0)a1(f1)
= Σ_f Π_i=1,2 ai(fi)
*)

(**
# Σを消す
 *)
(**
## 0を取り出す。

$$ \sum_{i \in \emptyset}a_i = 0 $$

総和をとる範囲が無い場合（0未満）は、単位元``0``になります。
 *)
  Lemma sum_nil a : \sum_(i < 0)(a i) = 0.
  Proof.
    by rewrite big_ord0.
  Qed.
  
(**
## ``a_0``項を取り出す。

$$ \sum_{i=0}^{0}a_i = a_0 $$

総和をとる範囲がひとつの項の場合（0以上0以下）は、``a 0`` となります。
 *)
  Lemma sum_nat1 a :
    \sum_(i < 1)(a i) = a ord0.
  Proof. by rewrite big_ord_recl big_ord0 addn0. Qed.

(**
``a ord_max`` でもあります。
*)  
  Lemma sum_nat1' a :
    \sum_(i < 1)(a i) = a ord_max.
  Proof. by rewrite big_ord_recr big_ord0. Qed.

(**
# インデックスを調整する補題
*)
(**
## 総和の範囲を0起源に振りなおす。(N/A)
*)

(**
# 最初の項、または、最後の項をΣの外に出す。
 *)
(**
## 最初の項をΣの外に出す。

総和の範囲の起点を変えずに、インデックスをずらします。

$$ \sum_{i=0}^{n}a_i = a_m + \sum_{i=0}^{n-1}a_{i + 1} $$
*)
  Lemma sum_first n a :
    \sum_(i < n.+1)(a i) = a ord0 + \sum_(i < n)(a (lift ord0 i)).
  Proof.
    by rewrite big_ord_recl.
  Qed.


(**
## 最後の項をΣの外に出す。

n(インデックスの上限)についての帰納法と組み合わせて使います。

$$ \sum_{i=0}^{n}a_i = \sum_{i=m}^{n-1}a_i + a_n $$
 *)
  Lemma sum_last n a :
    \sum_(i < n.+1)(a i) = \sum_(i < n)(a (widen_ord (leqnSn n) i)) + a ord_max.
  Proof.
    by rewrite big_ord_recr.
  Qed.

(**
## 数列の分割と結合 (N/A)
 *)
  
End Summation2.

(**
# 補足説明
 *)

(**
## 補題のサーチのしかた

このかたちでは、ほとんどヒットしない：
 *)
Search _ (\sum_ ( _ < _ ) _).

(**
一般的な表記を使うこと（スペースの位置にも注意）。
*)
Search _ (\big [ _ / _ ]_ ( _ <- _ | _ ) _).

Search _ (\big [ _ / _ ]_ ( _ < _ ) _).

(* END *)
