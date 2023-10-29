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
 *)

(* suhara *)
Search left_commutative.                    (* GRing.addrCA *)
Check GRing.addrCA.
Fail Check addrCA.
(* /suhara *)

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

(* suhara *)
Search left_commutative.                    (* addrCA *)
Check GRing.addrCA.
Check addrCA.
(* /suhara *)

(**
``Num`` をインポートすると、``Num.sqrt`` が  ``sqrt`` と書ける
ようになりますが、``nat``が上書きされてしまうため、これは避けることにします。
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
Check nat_num : qualifier 1 _.              (* Import Num すると、これが nat になってしまう。  *)
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

(* 以上 *)
