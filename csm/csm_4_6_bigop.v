(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.6 bigop.v --- 総和、相乗のライブラリ

======

2018_12_10 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import bigop matrix.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/bigop.v
*)

(**
# bigop とは

モノイド（単位元と、結合則を満たす二項演算がある）に対して、演算の繰り返しを可能とする。
*)

(**
# 用意されているモノイド
*)
(**
## 自然数
*)
(**
### モノイド

minn には単位元がないから、モノイドではない。
*)
Compute addn_monoid. (* = Monoid.Law addnA add0n addn0 : Monoid.law 0 *)
Compute maxn_monoid. (* = Monoid.Law maxnA max0n maxn0 : Monoid.law 0 *)
Compute muln_monoid. (* = Monoid.Law mulnA mul1n muln1 : Monoid.law 1 *)
Compute gcdn_monoid. (* = Monoid.Law gcdnA gcd0n gcdn0 : Monoid.law 0 *)
Compute lcmn_monoid. (* = Monoid.Law lcmnA lcm1n lcmn1 : Monoid.law 1 *)

(**
### bigop

\sum_ (Σ) と \pred_ (Π) と \max には専用のbigopが用意されている。
*)
Goal \big[addn/0]_(0 <= i < 5) i = \sum_(0 <= i < 5) i. Proof. done. Qed. (* Σ *)
Goal \big[maxn/0]_(0 <= i < 5) i = \max_(0 <= i < 5) i. Proof. done. Qed.
Goal \big[muln/1]_(0 <= i < 5) i = \prod_(0 <= i < 5) i. Proof. done. Qed. (* Π *)
Check \big[gcdn/0]_(0 <= i < 5) i.
Check \big[lcmn/1]_(0 <= i < 5) i.

(**
## 集合
*)
(**
### モノイド (finset.v で定義)
 *)
Compute setU_monoid.
(* = fun T : finType => Monoid.Law (setUA (T:=T)) (set0U (T:=T)) (setU0 (T:=T))
   : forall T : finType, Monoid.law set0 *)
Compute setI_monoid.
(* = fun T : finType => Monoid.Law (setIA (T:=T)) (setTI (T:=T)) (setIT (T:=T))
   : forall T : finType, Monoid.law [set: T] *)

(**
### インデックスのリストの例
*)
Definition p0 := [set x : 'I_5 | x <= 0] : {set 'I_5}.
Definition p1 := [set x : 'I_5 | x <= 1] : {set 'I_5}.
Definition p2 := [set x : 'I_5 | x <= 2] : {set 'I_5}.
Definition p3 := [set x : 'I_5 | x <= 3] : {set 'I_5}.
Definition p4 := [set x : 'I_5 | x <= 4] : {set 'I_5}.
Definition P5 := [:: p0; p1; p2; p3; p4].

(**
### bigop
*)
Goal \big[@setU (ordinal_finType 5)/set0]_(i <- P5) i = \bigcup_(i <- P5) i. done. Qed.
Goal \big[@setI (ordinal_finType 5)/setT]_(i <- P5) i = \bigcap_(i <- P5) i. done. Qed.

(**
## bool値
*)
(**
### モノイド
 *)
Compute andb_monoid. (* = Monoid.Law andbA andTb andbT : Monoid.law true *)
Compute orb_monoid.  (* = Monoid.Law orbA orFb orbF : Monoid.law false *)
Compute andb_monoid. (* = Monoid.Law andbA andTb andbT : Monoid.law true *)

(**
### インデックスのリストの例
*)
Definition B3 := [:: true; false; true].

(**
### bigop
*)
Check \big[andb/true]_(i <- B3) i.
Check \big[orb/false]_(i <- B3) i.
Check \big[addb/false]_(i <- B3) i.         (* exor *)

(**
## リスト
*)
(**
### モノイド
*)
Compute cat_monoid.
(* = fun T : Type => Monoid.Law (catA (T:=T)) (cat0s (T:=T)) (cats0 (T:=T))
     : forall T : Type, Monoid.law [::] *)

(**
### インデックスのリストの例
*)
Definition L := [:: [:: 0]; [::1]; [:: 2]]. (* リストのリスト *)
(* リストの要素には制約はない。 *)

(**
### bigop
*)
Check \big[cat/[::]]_(i <- L) i.

(*
# インデックスの範囲の表記
 *)


(*
インデックスの範囲の表記には2種類ある。それぞにオプションで条件を追加できる。

- リスト
- finType
*)

(**
## リストによる範囲の表記
*)
Definition s5o_l1 := \sum_(i <- [:: 0; 1; 2; 3; 4] | odd i) i.
Definition s5o_l2 := \sum_(i <- iota 0 5 | odd i) i.
Definition s5o_l3 := \sum_(0 <= i < 5 | odd i) i.

Goal s5o_l1 = s5o_l2. Proof. done. Qed.
Goal s5o_l2 = s5o_l3. Proof. done. Qed.
Goal s5o_l3 = s5o_l1. Proof. done. Qed.

(**
## finTypeによる範囲の表記
 *)
Definition s5o_t1 := \sum_(i in 'I_5 | odd i) i.
Definition s5o_t2 := \sum_(i : 'I_5 | odd i) i.
Definition s5o_t3 := \sum_(i < 5 | odd i) i.

Goal s5o_t1 = s5o_t2. Proof. done. Qed.
Goal s5o_t2 = s5o_t3. Proof. done. Qed.
Goal s5o_t3 = s5o_t1. Proof. done. Qed.

(**
表記ははenumを取り出すことで、リストで定義される。
ただし、相互に書き換えする一般的な方法はない。
*)
Goal s5o_l1 = s5o_t1. Proof. Abort.

(**
これは Coq では、ローカルに束縛された変数を含む式を外から書き換えられないため。
なので、どちらを使うか初めに決めるべきである。
とくに ``0 <= i < 5`` と ``i < 5`` は混ぜて使えないので、前者を使ったほうがよい。
*)

(**
# 総和についての補題（他のbigopでも成り立つ）
 *)
Section Summation1.
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
# 入れ子（ネスト）
 *)
(**
## ネストの入れ替え
*)
  Lemma exchamge_sum F m n :
    \sum_(0 <= i < m) (\sum_(0 <= j < n) F i j) =
    \sum_(0 <= j < n) (\sum_(0 <= i < m) F i j).
  Proof. by rewrite exchange_big. Qed.
  
(**
## 総和と総乗の可換についての補題（他の可換なopでも成り立つ）
*)
  Fail Lemma prod_distr_sum F m n :
    \prod_(0 <= i < m) (\sum_(0 <= j < n) F i j) =
    \sum_(f in _) (\prod_(0 <= i < m) F i (f i)).
  Proof.
    (* ********************************** *)
  Check bigA_distr_bigA.
    
(**
F(i, j) が F(i, f(i)) になっている。

こで、f は、 定義域 {0, 1}、値域 {0, 1, 2} である関数(finfun)のすべて。
全部で 3^2 = 9 個ある。
 *)

(**
Π_i=1,2 Σ_j=1,3 Fij
= (F00 + F01 + F02)(F10 + F11 + F12)
= F00 F10 + F00 F11 + F00 F12
+ F01 F10 + F01 F11 + F01 F12
+ F02 F10 + F02 F11 + F02 F12
= Σ_f F0(f0)F1(f1)
= Σ_f Π_i=1,2 Fi(fi)
*)

(**
# Σを消す
 *)
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
# インデックスを調整する補題
*)
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
# 最初の項、または、最後の項をΣの外に出す。
 *)
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

End Summation1.

(**
# 補足説明
 *)

(**
## 一般的な表記 （スペースの位置に注意）
 *)
Search _ "\big [ _ / _ ]_ ( _ <- _ | _ ) _".

(**
## 補題の定義

bigop.v で定義されている補題は、次のように見える。
*)
Check big_distrl : forall (R : Type) (zero : R) (times : Monoid.mul_law zero)
           (plus : Monoid.add_law zero times) (I : Type) (r : seq I) 
           (a : R) (P : pred I) (F : I -> R),
    times (\big[plus/zero]_(i <- r | P i) F i) a =
    \big[plus/zero]_(i <- r | P i) times (F i) a.

(**
ソースコードでは、ローカルに +, 0, -, 1 を定義して使っている：

Lemma big_distrl I r a (P : pred I) F :
  \big[+%M/0]_(i <- r | P i) F i * a = \big[+%M/0]_(i <- r | P i) (F i * a).
 *)

(**
# 追加の定理

$$ \sum_{i=m}^{p}a_i = \sum_{i=m}^{n}a_i + \sum_{i=n}^{p}a_i $$
 *)
Section Appendix.
  
  Lemma sum_cat' m n1 n2 a :
    \sum_(m <= i < m + n1 + n2) a i =
    \sum_(m <= i < m + n1) a i + \sum_(m + n1 <= i < m + n1 + n2) a i.
  Proof.
    rewrite -big_cat.
    f_equal.                       (* iインデックス部分を取り出す。 *)
    rewrite /index_iota.
    Check iota_add
      : forall m n1 n2 : nat, iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
    have -> : m + n1 + n2 - m = n1 + n2 by ssromega.
    have -> : m + n1 - m = n1 by ssromega.
    have -> : m + n1 + n2 - (m + n1) = n2 by ssromega.
    rewrite -iota_add.
    done.
  Qed.
  
  Lemma sum_cat m n p a :
    m <= n -> n <= p ->
    \sum_(m <= i < p) a i = \sum_(m <= i < n) a i + \sum_(n <= i < p) a i.
  Proof.
    move=> Hmn Hnp.
      by rewrite -big_cat_nat.
      
    Restart.
    move=> Hmn Hnp.                         (* omega が使う。 *)
    pose n1 := n - m.
    pose n2 := p - n.
    have -> : p = m + n1 + n2 by rewrite /n1 /n2; ssromega.
    have -> : n = m + n1 by rewrite /n1; ssromega.
      by apply: sum_cat'.
  Qed.
End Appendix.

(**
# 練習問題

https://staff.aist.go.jp/reynald.affeldt/ssrcoq/ssrcoq.pdf, p.137
https://staff.aist.go.jp/reynald.affeldt/ssrcoq/bigop_example.v
*)

Section Practice.
  
  Lemma exo34 n : 2 * (\sum_(0 <= x < n.+1) x) = n * n.+1.
  Proof.
    elim: n.
    - rewrite big_nat_recr //=.
      rewrite big_nil.
      rewrite muln0.
        by rewrite mul0n.
    - move=> n IH.
      rewrite big_nat_recr //=.  
      rewrite mulnDr.
      rewrite IH.
      rewrite -mulnDl.
      rewrite addn2.
        by rewrite mulnC.
  Qed.
  
  Lemma exo35 n : 6 * (\sum_(k < n .+1) k^2) = n * n.+1 * n.*2.+1.
  Proof.
  Admitted.
  
  Lemma exo36 (x n : nat) :
    1 < x -> (x - 1) * (\sum_(k < n .+1) x ^ k) = x ^ n .+1 - 1.
  Proof.
  Admitted.
  
  Lemma exo37 (v : nat -> nat ) (v0 : v 0 = 1)
        (vn : forall n, v n.+1 = \sum_(k < n .+1) v k) (n : nat)  :
    n != 0 -> v n = 2 ^ n.-1.
  Proof.
  Admitted.
  
  Parameter n : nat.
  Parameters a b : 'I_n.
  Lemma bigA_distr_big_test : (a + b)^2 = a^2 + 2 * a * b + b^2.
  Proof.
  Admitted.

End Practice.
    
(* END *)
