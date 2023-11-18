(**
MathComp/algebra を使って証明をする場合のガイドライン - ProofCafe -
=======

2023_10_29 @suharahiromichi

# 目的

Coq で MathComp/algebra を使って、整数、分数や多項式を含む命題を証明することは、
それまでの自然数だけの場合にくらべて、格段に難度が上がるため、
ProofCafe では解説や議論をすすめることを容易にするために、
証明スクリプトのガイドラインを設けます。

以下において、suhara と /suhara で囲まれた範囲は説明であり、
実際のスクリプトには不要です。
*)

(**
# MathComp パッケージのインポート（読み込み）

MathComp2 の規則に従い、coq-elpi と coq-hierarchy-builder をインポートします。
MathComp2 のパッケージ（.voファイル) は、``all_`` の単位でまとめてインポートすることにします。
当然、``all_ssreflect`` と ``all_algebra`` は必須ですが、
必要に応じて ``all_field`` をインポートします。
 *)
From elpi Require Import elpi.              (* coq-elpi *)
From HB Require Import structures.          (* coq-hierarchy-builder. *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_field.     (* 必要な場合のみ *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
ssralgの範囲の機能を使う場合でも、``all_algebra`` をインポートする場合
と ``ssralg`` だけをインポートする場合で、挙動が異なる場合があり、
インポートは最低限にしたほうが見通しがよい場合もありますが、
とりあえず、``all_algebra`` で全体をインポートするように統一したいと思います。
 *)

(**
# モジュールのインポート（ssralgとssrnum）

文献[1] に従い、ssralgとssrnumのモジュールのうち、以下をインポートします。
これにより、addrCA などの補題が、``GRing.addrCA`` ではなく、``addrCA`` で使えるようになります。
補題にPostfixはつけたくないと思います。
 *)

(* suhara *)
Search left_commutative.                    (* GRing.addrCA *)
Check GRing.addrCA.
Fail Check addrCA.
(* /suhara *)

(* **************************** *)
Import Num.Def.
Import Num.Theory.
Import GRing.Theory.
(* **************************** *)

(* suhara *)
Search left_commutative.                    (* addrCA *)
Check GRing.addrCA.
Check addrCA.
(* /suhara *)

(**
``Num`` をインポートすると、``Num.sqrt`` が  ``sqrt`` と書けるようになります
が、``nat`` が上書きされてしまい、``Datatypes.nat`` と書かなければならないので、これは避けることにします。
同様に ``GRing`` もインポートしません。
なお、``Num`` をインポートしても、それにつられて ``Num.Theory`` がインポートされるわけではありません。
*)
(* suhara *)
Fail Check sqrt.
Check Num.sqrt.
Check @Num.sqrt (_ : rcfType) : (_ : rcfType) -> (_ : rcfType).

Check nat : Set.                            (* Coqとssreflectのnat *)
Check Datatypes.nat.                        (* Coqとssreflectのnat *)

Check @nat_num (_ : archiNumDomainType) : qualifier 1 (_ : archiNumDomainType).
(* Import Num. *)
(* Notation nat := @nat_num *)
Fail Check nat : qualifier 1 _.             (* Num のなかの nat *)
(* /suhara *)

(**
# Scope

scope の詳細は、``https://github.com/suharahiromichi/coq/blob/master/alg/alg_scope.v``
を参照してください。ここでは結論のみ記載します。

1. ``Open Scope``するのは、``ring_scope``のみとします。
*)

Open Scope ring_scope.

(**
2. デミリタや型アノテーションは乱用しない。

3. ``=``や``==``の両辺の型を明示するために``:>``を使用する。

4. 型変換演算子は必要に応じて使用する。
*)

(**
# モジュールのインポート（具体型）

補題を使うのに必要な場合は、当該モジュールをインポートする。

ssrint の例：
 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)

(**
# k-coq Exercise 3.5.1.

手始めに、平方根のある式の証明をしてみます。

``√(4 + 2 * √3) = √3 + 1``

を証明します。
 *)
Section RCF.
(**
rcfType 型の型 R を定義します。以降等式は ``_ = _ :> R`` で示す。

sqrt は、rcfType 型の型で定義されています。
*)
  Variable R : rcfType.
  
(**
以下の証明は、抽象的は RCF型で行うことに注意してください。

数値は以下の型をもつ定数であり、``0``や``1``が、環としての意味をもち、
また、自然数に変換できることを除いて、
数値（整数あるいは実数）としての意味を持ちません。
なので、計算はできず、``Num.sqrt 4`` が 2 であるわけではありません。
まして、``Num.sqrt 3`` は、1.732... ではありません。
*)
  Check 4 : R.
  Check 3 : R.
  Check 2 : nat.
  Check 1 : R.
  
  Check Num.sqrt : R -> R.
  Check Num.sqrt (4 : R) : R.
  
(**
``(√(4 + √3 * 2))^2 = 4 + √3 * 2 を証明する。
*)
  Lemma l1 : (Num.sqrt (4 + ((Num.sqrt 3) *+ 2))) ^+ 2 = 4 + ((Num.sqrt 3) *+ 2) :> R.
  Proof.
    Check sqr_sqrtr : forall (R : rcfType) (a : R), 0 <= a -> Num.sqrt a ^+ 2 = a.
    rewrite sqr_sqrtr //.
(**
ルートと2乗を外すのは簡単ですが、平方根の中身が正であることの証明が必要です。
 *)
    apply: addr_ge0 => //.
    rewrite mulrn_wge0 //.
    by rewrite sqrtr_ge0.
  Qed.

(**
``(√3 + 1)^2 = 4 + 2*√3`` を証明する。
*)
  Lemma l2 : (Num.sqrt 3 + 1) ^+ 2 = 4 + Num.sqrt 3 *+ 2 :> R.
  Proof.
(**
RCFの上では数の足し算が定義されていないため、simpl などでは計算できません。
半環上での``+ 1``の補題がありますから、これを使います。
*)
    Check @natr1 : forall (R : semiRingType) (n : nat), n%:R + 1 = n.+1%:R.
(*Check natr1 : forall (R : semiRingType) (n : nat), n%:R + 1 = (n.+1)%:R. *)
  (*                                                             ^^^^  *)
  (*                                                            自然数 *)
    have l3_1__4 : 3 + 1 = 4 :> R by rewrite natr1.
    rewrite sqrrD1 sqr_sqrtr //.
    rewrite addrAC l3_1__4.
    done.
  Qed.

(**
両辺をn乗しても等しい、という公理があるので使います。
*)
  Check eqrXn2 : forall (R : numDomainType) (n : Datatypes.nat) (x y : R),
      (0 < n)%N -> 0 <= x -> 0 <= y -> (x ^+ n == y ^+ n) = (x == y).
  
  Goal Num.sqrt (4 + Num.sqrt 3 *+ 2) = Num.sqrt 3 + 1 :> R.
  (* **** *)
  apply/eqP.
  Check (@eqrXn2 R 2 (Num.sqrt (4 + Num.sqrt 3 *+ 2)) (Num.sqrt 3 + 1)).
  rewrite -(@eqrXn2 R 2 _ _) //.
  - by rewrite l1 l2.
  - admit.
  - admit.
  Admitted.

End RCF.

(* 以上 *)
