(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.6 bigop.v --- 総和、相乗のライブラリ

======

2018_12_10 @suharahiromichi

2020_8_22 @suharahiromichi

2023_5_26 @suharahiromichi      mathcomp2

2024_1_8 @suharahiromichi       alg_tac
 *)

(* HB.about を実行しない場合は、HB のImportは不要です。 *)
From HB Require Import structures.          (* MathComp2 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify ring lra.
     
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/bigop.v

Coq:8.17.0, MathComp:2.0.0
*)

(**
# bigop とは

モノイド（単位元と、結合則を満たす二項演算がある）に対して、演算の繰り返しを可能とする。

実態は foldr である。
*)

Goal \sum_(i <- [:: 0; 1; 2; 3; 4] | odd i) i = 4.
Proof.
  rewrite unlock /bigop.
  (* reducebig 0 [:: 0; 1; 2; 3; 4] (fun i : nat => BigBody i addn (odd i) i) = 9 *)
  rewrite /reducebig /applybig.
  (* 
  foldr
    ((fun (body : bigbody nat nat) (x : nat) =>
      match body with
      | BigBody _ op true v => op v x
      | BigBody _ op false _ => x
      end) \o (fun i : nat => BigBody i addn (odd i) i))
    0
    [:: 0; 1; 2; 3; 4]
  = 4
   *)
(**  
[:: 0; 1; 2; 3; 4] の要素のそれぞれが、\oの右側の、
(fun i : nat => BigBody i addn (odd i) i) の i に渡される。たとえば

- 0 なら、(BigBody 0 addn false 0)
- 1 なら、(BigBody 1 addn true 1)
- 2 なら、(BigBody 2 addn false 2)
- 3 なら、(BigBody 3 addn true 3)
- 4 なら、(BigBody 4 addn false 4)

 となる。
 *)
(**
これが\o の左側のbody に渡される。
BigBody は、（listのconsと同じ）値コンストラクタなので、要素どうしが対応して、
(BigBody 1 addn true 1) の場合なら、

- op <= addn
- true <= true
- v <= 1

から、(fun x => addn 1 x) が foldr に渡される。同様に、

- 0 なら (fun x => x)
- 1 なら (fun x => addn 1 x)
- 2 なら (fun x => x)
- 3 なら (fun x => addn 3 x)
- 4 なら (fun x => x)

以上から、
 *)
  Compute ((fun x => x)
             ((fun x => addn 1 x)
                ((fun x => x)
                   ((fun x => addn 3 x)
                      ((fun x => x)
                         0))))).            (* 4 *)
  rewrite /=.
  (* 1 + (3 + 0) = 4 *)
  done.
(**
コンストラクタ BigBody を用意する理由は、math-comp-book の 5.8 を参照のこと。
*)
Qed.  

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
(* mathcomp1 *)
(*
Compute addn_monoid. (* = Monoid.Law addnA add0n addn0 : Monoid.law 0 *)
Compute maxn_monoid. (* = Monoid.Law maxnA max0n maxn0 : Monoid.law 0 *)
Compute muln_monoid. (* = Monoid.Law mulnA mul1n muln1 : Monoid.law 1 *)
Compute gcdn_monoid. (* = Monoid.Law gcdnA gcd0n gcdn0 : Monoid.law 0 *)
Compute lcmn_monoid. (* = Monoid.Law lcmnA lcm1n lcmn1 : Monoid.law 1 *)
*)
(* mathcomp2 *)
HB.about addn.
HB.about maxn.
HB.about muln.
HB.about gcdn.
HB.about lcmn.

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
(* mathcomp1 *)
(*
Compute setU_monoid.
(* = fun T : finType => Monoid.Law (setUA (T:=T)) (set0U (T:=T)) (setU0 (T:=T))
   : forall T : finType, Monoid.law set0 *)
Compute setI_monoid.
(* = fun T : finType => Monoid.Law (setIA (T:=T)) (setTI (T:=T)) (setIT (T:=T))
   : forall T : finType, Monoid.law [set: T] *)
*)
(* mathcomp2 *)
HB.about setU.
HB.about setI.

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
(*
Goal \big[@setU (ordinal_finType 5)/set0]_(i <- P5) i = \bigcup_(i <- P5) i. done. Qed.
Goal \big[@setI (ordinal_finType 5)/setT]_(i <- P5) i = \bigcap_(i <- P5) i. done. Qed.
 *)
Goal \big[@setU (ordinal 5)/set0]_(i <- P5) i = \bigcup_(i <- P5) i. done. Qed.
Goal \big[@setI (ordinal 5)/setT]_(i <- P5) i = \bigcap_(i <- P5) i. done. Qed.

(**
## bool値
*)
(**
### モノイド
 *)
(* mathcomp1 *)
(*
Compute andb_monoid. (* = Monoid.Law andbA andTb andbT : Monoid.law true *)
Compute orb_monoid.  (* = Monoid.Law orbA orFb orbF : Monoid.law false *)
Compute addb_monoid. (* = Monoid.Law addbA addFb addbF : Monoid.law true *)
*)
(* mathcomp2 *)
HB.about andb.
HB.about orb.
HB.about addb.

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
(* mathcomp1 *)
(*
Compute cat_monoid.
(* = fun T : Type => Monoid.Law (catA (T:=T)) (cat0s (T:=T)) (cats0 (T:=T))
     : forall T : Type, Monoid.law [::] *)
*)
(* mathcomp2 *)
HB.about cat.

(**
### インデックスのリストの例
*)
Definition L := [:: [:: 0]; [::1]; [:: 2]]. (* リストのリスト *)
(* リストの要素には制約はない。 *)

(**
### bigop
*)
Check \big[cat/[::]]_(i <- L) i.

(**
## モノイドについての補足説明

monoid は、単位元が存在し、結合律が成り立つ。

(1) 可換律の成り立つ comoid と、分配則の成り立つ addoid も定義されている。
(2) これらの定義のしかたは Telescopes と呼ぶ。
MathComp 本体の Packed Class と異なるが共存できる。math-comp-book の 7.2 を参照のこと。
 *)
(* mathcomp1 *)
(*
Compute addn_comoid. (* = Monoid.ComLaw addnC         : Monoid.com_law 0 *)
Compute addn_addoid. (* = Monoid.AddLaw mulnDl mulnDr : Monoid.add_law 0 muln *)
*)
(* mathcomp2 *)
HB.about addn.

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
Definition s5o_l1 := \sum_(i <- [:: 0; 1; 2; 3; 4] | odd i) i. (* リスト直接 *)
Definition s5o_l2 := \sum_(i <- iota 0 5 | odd i) i.           (* iota *)
Definition s5o_l3 := \sum_(0 <= i < 5 | odd i) i.              (* 範囲 *)
Check @bigop nat nat O (index_iota O 5)
  (fun i : nat => @BigBody nat nat i addn (odd i) i).
Check bigop O (index_iota O 5)
  (fun i : nat => BigBody i addn (odd i) i). (* BigBodyはコンストラクタ *)
(* i の型が nat,
   インデックスのリストが inidex_iota 0 5 *)

(* 上記の3種類が同じである。 *)
Goal s5o_l1 = s5o_l2. Proof. done. Qed.
Goal s5o_l2 = s5o_l3. Proof. done. Qed.
Goal s5o_l3 = s5o_l1. Proof. done. Qed.

(**
## finTypeによる範囲の表記
 *)
Definition s5o_t1 := \sum_(i in 'I_5 | odd i) i. (* 注 *)
Definition s5o_t2 := \sum_(i : 'I_5 | odd i) i.
Definition s5o_t3 := \sum_(i < 5 | odd i) i.
Check @bigop nat 'I_5 O (index_enum (ordinal 5))
  (fun i : 'I_5 => @BigBody nat 'I_5 i addn (odd (nat_of_ord i)) (nat_of_ord i)).
Check bigop O (index_enum (ordinal 5))
  (fun i : 'I_5 => BigBody i addn (odd i) i).
(**
i の型が 'I_5 のとき
index_enum は Ordinal 型を要素とするリストを返す。
 *)
Check index_enum (ordinal 5) : seq (ordinal 5).

(* 注： @BigBody の第5引数が、odd (nat_of_ord i) から、
   andb (i \in 'I_5) (odd (nat_of_ord i)) になる。 *)
         
(* 上記の3種類が同じである。 *)
Goal s5o_t1 = s5o_t2. Proof. done. Qed.
Goal s5o_t2 = s5o_t3. Proof. done. Qed.
Goal s5o_t3 = s5o_t1. Proof. done. Qed.

(**
## 2種類の表記の間の書き換え

``0 <= i < 5`` から ``i < 5`` へは、相互に書き換えできる。
*)
Goal s5o_l3 = s5o_t3.
Proof.
  rewrite /s5o_l3 /s5o_t3.
  Check big_mkord
     : forall (R : Type) (idx : R) (op : R -> R -> R) (n : nat)
         (P : pred nat) (F : nat -> R),
       \big[op/idx]_(0 <= i < n | P i) F i = \big[op/idx]_(i < n | P i) F i.
  rewrite big_mkord.
  done.
Qed.

(**
（重要）以下においては、リスト形式の

``\sum_(m <= i < n) a i`` または ``\sum_(m <= i < n.+1) a i`` の形式を使います。

命題によっては、``m < n`` または ``m <= n`` の条件が必要になる場合があります。
この範囲を満たさない場合は、単位元の0になってしまうためです（後述）。

また ``0 <= i`` の場合もそれを略さないようにします（略すと finType形式になってしまうため）。
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

\sum_{i=m}^{n-1} c = (n - m) c \\

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

  Lemma sum_cinst m n c :
    \sum_(m <= i < n) c = (n - m) * c.
  Proof. by rewrite sum_nat_const_nat. Qed.
(**
# Σの中身の書き換え

Σの中の i は、ローカルに束縛されている（ラムダ変数である）ので、
直接書き換えることはできません。一旦、取り出して書き換えることになります。
 *)
  Lemma eq_sum m n a b : a =1 b ->
                         \sum_(m <= i < n)(a i) = \sum_(m <= j < n)(b j).
  Proof.
    move=> Hab.                             (* =1 は第1階の=です。 *)
    apply: eq_big_nat => i Hmn.
    by rewrite Hab.
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
    \sum_(0 <= i < m) (\sum_(0 <= j < n) (a i j)) =
    \sum_(0 <= j < n) (\sum_(0 <= i < m) (a i j)).
  Proof. by rewrite exchange_big. Qed.
  
(**
## ネストの入れ替え（総和と総乗の場合）

$$ \prod_{i=0}^{m-1}(\sum_{j=0}^{n-1)} a_{i j} =
   \sum_{j=0}^{n-1}(\prod_{i=0}^{m-1)} a_{i j} $$
*)
  (* F : 'I_m -> 'I_n -> _ なので、aより前にmとnを定義しないといけない。 *)
  Lemma prod_distr_sum' m n a :
    \prod_(0 <= i < m) (\sum_(0 <= j < n) (a i j)) =
    \sum_(0 <= j < n) (\prod_(0 <= i < m) (a i j)).
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
      have -> : n - m = 0 by lia.
      done.
    - rewrite H.
      by rewrite big_nil.
  Qed.

(**
なお ``0 <=`` は必ず成り立ちます。自然数領域で扱っているため、
*)
  Goal forall m n a, 0 <= \sum_(m <= i < n) a i.
  Proof. done. Qed.
  
(**
## ``a_n``項を取り出す。

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
    have -> : n + m - m = n by lia.
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

n(インデックスの上限)についての帰納法と組み合わせて使います。

$$ \sum_{i=m}^{n}a_i = \sum_{i=m}^{n-1}a_i + a_n $$
 *)
  Lemma sum_last m n a :
    m <= n ->
    \sum_(m <= i < n.+1)(a i) = \sum_(m <= i < n)(a i) + a n.
  Proof.
    move=> Hmn.
    by rewrite big_nat_recr.
  Qed.

(**
## 数列の分割と結合

$$ \sum_{i=m}^{p-1}a_i = \sum_{i=m}^{n-1}a_i + \sum_{i=n}^{p-1}a_i $$
 *)
  Lemma sum_cat' m n1 n2 a :
    \sum_(m <= i < m + n1 + n2) a i =
    \sum_(m <= i < m + n1) a i + \sum_(m + n1 <= i < m + n1 + n2) a i.
  Proof.
    rewrite -big_cat.
    f_equal.                       (* iインデックス部分を取り出す。 *)
    rewrite /index_iota.
    Check iotaD                             (* mathcomp2 *)
      : forall m n1 n2 : nat, iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
    have -> : m + n1 + n2 - m = n1 + n2 by lia.
    have -> : m + n1 - m = n1 by lia.
    have -> : m + n1 + n2 - (m + n1) = n2 by lia.
    rewrite -iotaD.
    done.
  Qed.
  
  (* big_cat_nat を使えば、直接証明できる。 *)
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
    have -> : p = m + n1 + n2 by rewrite /n1 /n2; lia.
    have -> : n = m + n1 by rewrite /n1; lia.
    by apply: sum_cat'.
  Qed.

End Summation1.

(**
# 補足説明
 *)

(**
## 補題のサーチのしかた

このかたちでは、ほとんどヒットしない：
 *)
Search _ (\sum_ ( _ <= _ < _ ) _).

(**
一般的な表記を使うこと（スペースの位置にも注意）。
*)
Search _ (\big [ _ / _ ]_ ( _ <- _ | _ ) _).

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
## math-comp-book の関連箇所

[https://math-comp.github.io]

- 5.7 The generic theory of \big" operators
- 5.7.1 The generic notation for foldr
- 5.7.2 Assumptions of a bigop lemma
- 5.7.3 Searching the bigop library
- 5.8 Stable notations for big operators
- 5.9 Working with overloaded notations
- 7.2 Telescopes
*)

(**
# 練習問題

[https://staff.aist.go.jp/reynald.affeldt/ssrcoq/ssrcoq.pdf], p.137
[https://staff.aist.go.jp/reynald.affeldt/ssrcoq/bigop_example.v]
*)
Section Practice.
  
(**
$$ 2 (\sum_{x=0}^{n} x) = n (n + 1) $$
*)
  Lemma exo34 n : 2 * (\sum_(0 <= x < n.+1) x) = n * n.+1.
  Proof.
    elim: n => [| n IH].
    - rewrite sum_last //=.                 (* big_nat_recr *)
      rewrite sum_nil //=.                  (* big_nil *)
    - rewrite sum_last //=.                 (* big_nat_recr *)
      rewrite mulnDr.
      rewrite IH.
      rewrite -mulnDl.
      rewrite addn2.
      rewrite mulnC.
      done.
  Qed.
  
(**
$$ 6 (\sum_{k=0}^{n} k^{2}) = n (n + 1) (2 n + 1) $$
*)
  (* これまでに証明した補題が使えるので、nat 形式にする。 *)
  Lemma exo35' n : 6 * (\sum_(0 <= k < n.+1) k^2) = n * n.+1 * n.*2.+1.
  Proof.
    elim: n => [| n IHn].
    + by rewrite sum_nat1.
    + rewrite sum_last //=.
      
      rewrite mulnDr IHn.
      (* n * n.+1 * n.*2.+1 + 6 * n.+1 ^ 2 = n.+1 * n.+2 * (n.+1).*2.+1 *)
      (* 両辺とも  (n + 1)(2n^2 + 7n + 6) である。 *)

      (* n.+1 を括り出す。 *)
      rewrite -[RHS]mulnA.
      rewrite [6 * n.+1 ^ 2]mulnC -mulnn.
      rewrite [n * n.+1]mulnC.
      rewrite -[n.+1 * n * n.*2.+1]mulnA.
      rewrite -[n.+1 * n.+1 * 6]mulnA.
      rewrite -[LHS]mulnDr.
      congr (_ * _).

      (* .+2 と .+1 を外す。 *)
      rewrite -[n.+2]addn2.
      rewrite -[n.+1]addn1.
      rewrite -[n.*2.+1]addn1.
      rewrite -[(n + 1).*2.+1]addn1.
      rewrite -[(n + 1).*2]muln2.

      (* 左辺を展開して簡約する。 *)
      rewrite [in LHS]mulnDr [in LHS]mulnDl [in LHS]muln1 [in LHS]mul1n.
      have -> : n * n.*2 + n + (n * 6 + 6) = n * n.*2 + n * 7 + 6 by lia.
      
      (* 右辺を展開して簡約する。 *)
      rewrite ![in RHS]mulnDl ![in RHS]mulnDr [in RHS]mul1n [in RHS]muln1.
      rewrite [in n * (n * 2)]muln2.
      have -> : n * n.*2 + n * 2 + n + (2 * (n * 2) + 2 * 2 + 2)
                = n * n.*2 + n * 7 + 6 by lia.
      done.
  Qed.

  (* 出題の k > n.+1 の形式で証明する。 *)
  Lemma exo35 n : 6 * (\sum_(k < n.+1) k^2) = n * n.+1 * n.*2.+1.
  Proof. by rewrite -exo35' big_mkord. Qed.
  
  
(**
等比数列の和の公式 @morita_hm さん

$$ (x-1) \sum_{k=0}^{n} x^{k} = x^{n+1} - 1 $$
 *)
  Lemma exo36' (x n : nat) :
    1 < x -> (x - 1) * (\sum_(0 <= k < n.+1) x^k) = x^(n.+1) - 1.
  Proof.
    move=> Hxp.
    elim: n => [| n IHn].
    - rewrite sum_nat1 //=.
        by rewrite expn0 expn1 muln1.
    - rewrite sum_last //=.
      rewrite mulnDr IHn.
      rewrite addnBAC.
      + have -> : x ^ n.+1 + (x - 1) * x ^ n.+1 = (1 + (x - 1)) * x ^ n.+1
          by rewrite mulnDl mul1n.
        rewrite subnKC.
        * by rewrite -expnS.
        * lia.
      + have H : n.+1 < x ^ n.+1 by apply: ltn_expl. (* 0 < x ^ n.+1 の証明 *)
        lia.
  Qed.
  
  Lemma exo36 (x n : nat) :
    1 < x -> (x - 1) * (\sum_(k < n.+1) x^k) = x^(n.+1) - 1.
  Proof.
    move=> Hxp.
      by rewrite -exo36' // big_mkord.
  Qed.


(**
```math
\forall v,
[[v_0 = 1 \wedge \forall n, [v_{n + 1} = \sum_{k=0}^{n} v_k]]
\longrightarrow
\forall n, [n \neq 0 \rightarrow v_n = 2^{n-1}]]
```

``∀v`` は全体に係っていますが、
``∀n``は前提と結論のそれぞれ、別々に係っている（別物）ことに注意してください。

須原補足：問題では、vの場合分けにラベルが付与されていて、ふたつめのn(ゴールのn)が、
補題の引数になっているので、論理式が読み難くなっていますが、数学的には上記のとおりです。

以下 @morita_hm さん

この命題は以下の2項間漸化式:
    v 1 = 1,
    v n.+1 = v n + v n
に言い換えられることに気付けば以下のような証明が可能になります
 *)

(**
```math
\forall v,
[[v_0 = 1 \rightarrow \forall n, [v_{n+1} = \sum_{k=0}^{n} v_k]]
\longrightarrow
v_1 = 1]
```
*)
  (* v 1 = 1 を証明 *)
  Lemma exo37_v_1 (v : nat -> nat ) (v0 : v 0 = 1)
        (vn : forall n, v n.+1 = \sum_(0 <= k < n.+1) v k) : (* (n : nat) *)
    v 1 = 1.
  Proof.
    rewrite (vn 0).
    rewrite sum_last.
    - rewrite sum_nil.
      + by rewrite add0n.
      + lia.
    - lia.
  Qed.
  
(**
```math
\forall v,
[[v_0 = 1 \rightarrow \forall n, [v_{n+1} = \sum_{k=0}^{n} v_k]]
\longrightarrow
\forall n, [n \neq 0 \rightarrow v_{n+1} = v_n + v_n]]
```
*)
  (* \sum を消去して隣接2項間漸化式をつくる *)
  Lemma exo37_rec_formula (v : nat -> nat ) (v0 : v 0 = 1)
        (vn : forall n, v n.+1 = \sum_(0 <= k < n.+1) v k) (n : nat)  :
    n != 0 -> v n.+1 = v n + v n.
  Proof.
    move=> Hnp.
    rewrite vn sum_last //=.
    have <- : v n = \sum_(0 <= k < n) v k
      by rewrite -[n]prednK; [rewrite (vn n.-1) | rewrite lt0n].
    done.
  Qed.

  Lemma exo37_rec_formula' (v : nat -> nat ) (* 予備 *)
        (v0 : v 0 = 1) (vn : forall n, v n.+1 = v n + v n) (n : nat) :
    v n = 2 ^ n.
  Proof.
    elim: n => [|n IHn].
    - rewrite expn0.
      exact v0.
    - rewrite vn.
      rewrite IHn.
      have -> : 2 ^ n = 1 * 2^ n by rewrite mul1n.
      rewrite -mulnDl.
      have -> : 1+1 = 2 by [].
      by rewrite expnS.
  Qed.
  
  (* 本題の証明 *)
  Lemma exo37' (v : nat -> nat ) (v0 : v 0 = 1)
        (vn : forall n, v n.+1 = \sum_(0 <= k < n.+1) v k) (n : nat)  :
    n != 0 -> v n = 2^n.-1.
  Proof.
    elim: n => [|k IHk].
    - done.                                 (* 証明の対象外  *)
    - elim k => [|l IHl].                   (* v 1 からの帰納法 *)
      + move=> H1.
        rewrite //= expn0.
        by apply: exo37_v_1.
      + move=> Hp.
        move/exo37_rec_formula in vn.
        rewrite vn.
        * rewrite IHl //=.
          have -> : 2 ^ l = 1 * 2^ l by rewrite mul1n.
          rewrite -mulnDl.
          have -> : 1+1 = 2 by [].
          by rewrite expnS.
        * done.
    - done.
  Qed.
  
  (* 出題の k > n.+1 の形式で証明する。 *)
  Lemma exo37 (v : nat -> nat) (v0 : v 0 = 1)
        (vn : forall n, v n.+1 = \sum_(k < n.+1) v k) (n : nat)  :
    n != 0 -> v n = 2^n.-1.
  Proof.
    move=> Hn.
    apply: exo37' => // n'.
    by rewrite big_mkord.
  Qed.
  
(**
須原補足：exo37 の式は練習問題のとおりですが、
v0 と vn にラベルが付いていて、逆に式が読みにくいと思います。
数学の教科書にある書き方に近づけて、次のように書く方がよいのではないかと思います。
    
v0 や vn のラベルは intro するときに指定すればよいので省略し、
ふたつめのn(ゴールにだけ係るn)も、ゴールだけの∀としました。
 *)
  Lemma exo37_suhara (v : nat -> nat) :
    v 0 = 1 /\ (forall n, v n.+1 = \sum_(k < n.+1) v k) ->
    forall n, n != 0 -> v n = 2^n.-1.
  Proof.
    move=> [v0 vn] n Hn.                    (* 一旦introすれば、 *)
    by apply: exo37.                        (* 同じである。 *)
  Qed.
  
(**
XXX
*)  
  Parameter n : nat.
  Parameters a b : 'I_n.
  Lemma bigA_distr_big_test : (a + b)^2 = a^2 + 2 * a * b + b^2.
  Proof.
  Admitted.
End Practice.

(**
# 問題 - 自然数 n が合成数なら、メルセンヌ数 $ M_{n} = 2^{n} - 1 $
も合成数であることを証明してください。

実際には、nが、2以上の任意の2自然数に積であるとき（すなわち合成数であるとき）、
$ 2^{n} -1 $ もふたつの自然数の積（合成数）であることを証明します。

また、合成数の定義は、「それより小さい、ふたつの正の整数の積で表される整数」
ですが、ここでは、「ふたつの 2以上の自然数 の積で表される自然数」としています。
これは同値です（おまけを参照）。


[a] https://ja.wikipedia.org/wiki/メルセンヌ数
 *)
Section Composite_Number.

(**
最初に補題として、[a] にも掲載されている次式を証明します。
これは、a と b は自然数で、$1 \le a$ であれば成り立ちます。

$$ (2^{b} - 1) \sum_{i=0}^{a-1} 2^{i b} = 2^{a b} - 1, ただし 1 \le a $$
*)
  Lemma l_e2_ab_1 a b :
    1 <= a ->
    (2^b - 1) * (\sum_(0 <= i < a) 2^(i * b)) = 2^(a * b) - 1.
  Proof.
    move=> Ha.
    
    (* 左辺を展開する。 *)
    rewrite mulnBl.
    
    (* 左辺、第1項 *)
    rewrite -sum_distrr //=.
    have H : \sum_(0 <= i < a) 2 ^ b * 2 ^ (i * b) = \sum_(0 <= i < a) 2 ^ (i.+1 * b).
    by apply: eq_sum => i; rewrite -expnD mulnC -mulnS mulnC.
    rewrite H.
    rewrite -(sum_add1 a (fun x => 2 ^ (x * b))).
    rewrite [\sum_(1 <= i < a.+1) 2 ^ (i * b)]sum_last //=.
    (* \sum_(1 <= i < a) 2 ^ (i * b) + 2 ^ (a * b) *)
    
    (* 左辺、第2項 *)
    rewrite  mul1n.
    rewrite [\sum_(0 <= i < a) 2 ^ (i * b)]sum_first //=.
    rewrite mul0n expn0.
    rewrite [1 + \sum_(1 <= i < a) 2 ^ (i * b)]addnC.
    (* - (\sum_(1 <= i < a) 2 ^ (i * b) + 1) *)
    
    (* 左辺を整理する。 *)
    rewrite subnDl.
    (* 2 ^ (a * b) - 1 *)
    
    (* 左辺と右辺が同じ。 *)
    done.
  Qed.

(**
証明の概要：

証明したい命題
「nが、2以上の任意の2自然数に積であるとき
（すなわち合成数であるとき）、$2^{n} - 1$ もふたつの自然数の積（合成数）である」
をもうすこし噛み砕くと、

aとbが2以上の任意の自然数であるとき、適当な2以上の自然数xとyが存在して、

$$ 2^{a * b} - 1 = x y $$

が成り立つ、ということになります。ここで、 $ n = a b $ としています。

そして、適当な x と y について具体的に以下を代入すると、

```math

x = 2^{b} - 1 \\
y = \sum_{i=0}^{a-1}2^{i b}

```

先に証明した補題の式が得られます。

$$ (2^{b} - 1) \sum_{i=0}^{a-1}2^{i b} = 2^{a b} - 1 $$

普通は、これで自明とするのですが、
2以上のaとbに対して、xとyもまた2以上であることを示すことも忘れてはいけません。
それも、別の補題として証明しておきます。
*)  
  
  (* 何か所かで使う補題。 *)
  Lemma le2_le1 a : 2 <= a -> 1 <= a.       (* 1 < a -> 0 < a *)
  Proof. move=> H. by rewrite ltnW. Qed.    (* lia でも解ける。 *)
  
  (* 2 <= x を証明する補題： *)
  Lemma e2b_1_ge2 b : 2 <= b -> 2 <= 2^b - 1. (* 1 < b -> 1 < 2^b - 1 *)
  Proof.
    move=> H.
    rewrite ltn_subRL addn1.
    rewrite -{1}(expn1 2).
    by rewrite ltn_exp2l.
  Qed.
  
  (* 2 <= y を証明する補題： *)  
  Lemma sum0_2_e2ib a b :
    2 <= a -> 2 <= b -> 2 <= \sum_(0 <= i < a) 2 ^ (i * b).
  Proof.
    move=> Ha Hb.
    rewrite sum_first; last by apply: le2_le1.
    rewrite sum_first; last done.
    have H1 : 1 <= 2 ^ (0 * b) by rewrite mul0n expn0.
    have H2 : 1 <= 2 ^ (1 * b) by rewrite mul1n expn_gt0 orb_idr.
    have H3 : 0 <= \sum_(2 <= i < a) 2 ^ (i * b) by done. (* 0以上は自明。 *)
    lia.
  Qed.
  
  (* 証明したいもの *)
  Lemma e2_ab_1_composite (a b : nat) :
    2 <= a -> 2 <= b ->
    exists (x y : nat), 2 <= x /\ 2 <= y /\ (x * y = 2^(a * b) - 1).
  Proof.
    move=> Ha Hb.
    exists (2 ^ b - 1), (\sum_(0 <= i < a) 2 ^ (i * b)).
    split ; [| split].
    - by apply: e2b_1_ge2.    (* 2 <= x を証明する。 *)
    - by apply: sum0_2_e2ib.  (* 2 <= y を証明する。 *)
    - move/le2_le1 in Ha.     (* 前提を 2 <= a から 1 <= a にする。 *)
      by apply: l_e2_ab_1.    (* x * y = ... を証明する。 *)
  Qed.

(**
## おまけ 合成数の定義についての補題

「ある自然数が、より小さいふたつの自然数の積で表されるとき、
そのふたつの自然数は1より大きい」ということを証明します。
 *)  

(**
「2以上」は、「1を越える」、と表記(Notation)だけが異なります。
「1を越える」ほうが表記として複雑なので、Coqの清書系はそちらをつかいます。
これに留意して、ここでは $1 \lt m$ の方を使います。
*)
  Check 2 <= 10.                            (* 1 < 10 *)
  
  Lemma l_1m1n_mmn (m n : nat) : 1 < m -> 1 < n -> m < m * n.
  Proof.
    move=> Hm Hn.
    rewrite ltn_Pmulr //.
    lia.                                    (* 1 < m -> 0 < m *)
  Qed.
  
  Lemma l_1m1n_nmn (m n : nat) : 1 < m -> 1 < n -> n < m * n.
  Proof.
    move=> Hm Hn.
    rewrite ltn_Pmull //.
    lia.                                    (* 1 < n -> 0 < n *)
  Qed.
  
  Lemma l_nmn_1m (m n : nat) : n < m * n -> 1 < m.
  Proof.
    rewrite -{1}[n]mul1n ltn_mul2r.
    by case/andP.
  Qed.
  
  Lemma l_mmn_1n (m n : nat) : m < m * n -> 1 < n.
  Proof.
    rewrite -{1}[m]muln1 ltn_mul2l.
    by case/andP.
  Qed.

  Lemma l_composite_hypo (m n : nat) :
    ((m < m * n) && (n < m * n)) = ((1 < m) && (1 < n)).
  Proof.
    apply/andP/andP; case=> Hm Hn; split.
    - by apply: l_nmn_1m Hn.
    - by apply: l_mmn_1n Hm.
    - by apply: l_1m1n_mmn.
    - by apply: l_1m1n_nmn.
  Qed.

End Composite_Number.

(* END *)
