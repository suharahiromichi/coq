(**
ssrnum.v サンプル
*)
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
From mathcomp Require Import ssralg ssrnum.

(**
# 型の階層図
*)

(**
```
                       zmodType Z加群 アーベル群
                       |\
                       | +-------------------+
                       |                      \
idomainType 整域       porderZmodType          normedZmodType
|\                     |                      /
| +------------------+ | +-------------------+
|                     \|/
fieldType 体           numDomainType
|\                     |\
| +------------------+ | +-------------------+
|                     \|                      \
closedField 閉体       numFieldType            realDomainType ~~~ (int)
|                      |                      /
|                      | +-------------------+
|                      |/
numClosedFieldType     realFieldType 実体
~~~~                   |\
(algC)                 | +---------------------archiFieldType ~~~ (rat)
                       |
                       |
                       rcfType (Real Closed Field) 実閉体
```
- num...Type は、normとorderのある型

- real...Type は、要素は正か負である型

- archi...Type は、アルキメデスの公理が成り立つ型（ノルムに上限がある）

- RCF 実閉体 までくると、平方根が使えるので、その証明をしてみる。
*)
Check Num.sqrt : (_ : rcfType) -> (_ : rcfType).

Import GRing.Theory.
Import Num.
Import Num.Theory.
Import Num.Def.

Local Open Scope ring_scope.

(**
# k-coq Exercise 3.5.1.

``√(4 + 2 * √3) = √3 + 1``

を証明します。
sqrt は、rcfType 型の型で定義されています。
 *)
Check sqrt 4 : (_ : rcfType).

Section RCF.
(**
rcfType 型の型 R を定義します。以降等式は ``_ = _ :> R`` で示す。
*)
Variable R : rcfType.

(**
数値は自然数から R 型へのコアーションになるが、それは定義されていないので、フルに書くと以下になる。
*)
Check (@GRing.natmul (GRing_SemiRing__to__GRing_Nmodule (Num_RealClosedField__to__GRing_SemiRing R))
         (GRing.one (Num_RealClosedField__to__GRing_SemiRing R)) (S (S (S (S O))))).
(**
実際には、型注釈で済ますことができる。
*)
Check 4 : R.

(**
まず、平方根の2乗の証明をします。
*)
Lemma l1 : (sqrt (4 + sqrt 3 *+ 2)) ^+ 2 = 4 + sqrt 3 *+ 2 :> R.
Proof.
  Check sqr_sqrtr : forall (R : rcfType) (a : R), 0 <= a -> sqrt a ^+ 2 = a.
  rewrite sqr_sqrtr //.
(**
平方根の中身が正であることの証明が必要です。
 *)
  apply: addr_ge0 => //.
  rewrite mulrn_wge0 //.
  by rewrite sqrtr_ge0.
Qed.

(**
RCFの上では（まだ）数の足し算が定義されていないため、simpl などでは計算できません。
半環上での``+ 1``の補題がありますから、これを使います。
*)
Lemma l3_1__4 : 3 + 1 = 4 :> R.
Proof.
  Check natr1 : forall (R : semiRingType) (n : nat), n%:R + 1 = (n.+1)%:R.
  (*                                                             ^^^^  *)
  (*                                                            自然数 *)
  by rewrite natr1.
Qed.

(**
``(√3 + 1)^2 = 4 + 2*√3`` を証明しておきます。
*)
Lemma l2 : (sqrt 3 + 1) ^+ 2 = 4 + sqrt 3 *+ 2 :> R.
Proof.
  rewrite sqrrD1 sqr_sqrtr //.
  rewrite addrAC l3_1__4.
  done.
Qed.

(**
両辺をn乗しても等しい、という公理があるので使います。
*)
Goal sqrt (4 + sqrt 3 *+ 2) = sqrt 3 + 1 :> R.
Proof.
  Check eqrXn2
    : forall (R : numDomainType) (n : nat) (x y : R),
      (0 < n)%N -> 0 <= x -> 0 <= y -> (x ^+ n == y ^+ n) = (x == y).
  apply/eqP.
  Check (@eqrXn2 R 2 _ _).
  rewrite -(@eqrXn2 R 2 _ _) //.
  - by rewrite l1 l2.
  - by rewrite sqrtr_ge0.
  - by rewrite addr_ge0 // sqrtr_ge0.
Qed.

(**
## 補足説明

sqrtは型を引数に取れるので、そのように使うこともできる。``:> R`` がいらなくなる。
*)
Check @sqrt R 4 : R.

Lemma l1'' : (@sqrt R (4 + @sqrt R 3 *+ 2)) ^+ 2 = 4 + @sqrt R 3 *+ 2.
Proof.
  rewrite sqr_sqrtr //.
  apply: addr_ge0 => //.
  rewrite mulrn_wge0 //.
  by rewrite sqrtr_ge0.
Qed.

(**
sqrtの引数に `` : R`` をつけてもよい。上記と同じことである。
*)
Lemma l1' : (sqrt ((4 + sqrt (3 : R) *+ 2) : R) : R) ^+ 2 = 4 + sqrt (3 : R) *+ 2.
Proof.
  rewrite sqr_sqrtr //.
  apply: addr_ge0 => //.
  rewrite mulrn_wge0 //.
  by rewrite sqrtr_ge0.
Qed.

End RCF.

(* END *)
