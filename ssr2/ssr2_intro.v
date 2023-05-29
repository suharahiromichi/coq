(**
MathComp2 の紹介
==============================
2023/05/30


@suharahiromichi


# 1. Mathematical Components 2.0.0 (MathComp2) の概要

- 型が Hierarchy Builder tool (HB) を使って定義されなおした。

- 内部構造が大きく変わっているが、Mathematical Components 1.7.x (MathComp1) との互換性は保たれている。

- 「型」や「型の型」を定義するコード以外は、ほとんど影響ない。

- MathComp1 も、Coq本体のバージョンアップに追随して、当面保守される。

- Mathematical Components Book は、Part II (6〜8章は obsolete)。

HB : λProlog のひとつの実装である Embeddable λProlog Interpreter (ELPI) を使って実装されている。
Coq-ELPI (Coq plugin embedding Elpi) を経由して呼び出される。


# 2. 参考資料

- GitHub

https://math-comp.github.io/


- リリースアナウンス

https://github.com/math-comp/math-comp/releases


- 移植ガイド

https://github.com/math-comp/math-comp/blob/master/etc/porting_to_mathcomp2/porting.pdf


- Math Comp School & Workshop - 2022 (Alpha版、lesson5 から)

https://mathcomp-schools.gitlabpages.inria.fr/2022-12-school/school


- Hierarchy Builder (HB)

https://github.com/math-comp/hierarchy-builder/


- λPRologの紹介

https://qiita.com/suharahiromichi/items/a046859da0c0883e7304


# 3. MathCompユーザーの立場から

MathCompユーザーの立場からみると、
変更は以下のようになります。

- 型の定義の箇所も、機械的に移植できる（後述）

- インストールには、ELPI、HB などが必要になる。
  型を定義しないなら、インポートは不要である。

- 型定義をおこなう箇所の実行が遅い。
  MathCompのコンパイルやインポートに影響する。

- algebra-tactcs (ring と field タクティク）が未対応である(2022/5/20現在)。

# 4. 型階層の変更の例

## 4.1 eqType から始まる型階層

階層関係（萩原先生の本を参照）やインスタンス関係は変更はありません。

```coq:MathComp1
Check 42 : nat        : Type.
Check 42 : nat_eqType : eqType.

```

```coq:MathComp2
Check 42 : nat        : Type.
Check 42 : nat        : eqType.

```

## 4.2 ΣやΠなどのbig operatorのためのモノイド

bigopの使い方は変更はありません。

```coq:MathComp1
Check addn        : nat -> nat -> nat.
Check addn_monoid : Monoid.law 0.
```

```coq:MathComp2
Check addn      : nat -> nat -> nat.
Check add       : Monoid.law 0.
```

# 5. MathCompで文字列型を定義する例

## 5.1 目標

以下を使えるようにしたい。
MathCompのEquality型のインスタンスとしてのstringを定義する。

```
Compute "ABC" == "ABC"          (* true *)
COmpute "ABC" == "AB"           (* false *)
```

## 5.2 Standard Coq の ``String`` にある定義

- string            文字列型
- String.eqb        文字列どうしのboolの等式
- String.eqb_spec   boolの等式が、Propの等式と同値であることの証明


## 5.3 Equality型のインスタンスの定義

以下のように、MathComp1 と MathComp2 の定義を見比べてみても、
``Canonical``コマンドが、``HB.instance`` に変わり、1行にまとまりましたが、
boolの等式がPropの等式と同値であることの証明を与えることに違いはありません。
実際に、機械的に移植することは可能でしょう。
なお、MathComp2 では、``HB``のインポートが必要です。


```coq:MathComp1
From mathcomp Require Import all_ssreflect.
Require Import String.
Open Scope string_scope.                (* 注1 *)

Definition string_eqMixin := EqMixin String.eqb_spec.   (* 注2 *)
Canonical string_eqType := EqType string string_eqMixin.

Check "ABC" : string        : Type.
Check "ABC" : string_eqType : eqType.
```
*)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Require Import String.
Open Scope string_scope.                (* 注1 *)

HB.instance Definition _ := hasDecEq.Build string String.eqb_spec.   (* 注2 *)

Check "ABC" : string        : Type.
Check "ABC" : string        : eqType.

(**
注1 ダブルクォーテーションで囲むことで文字列になります。
型注釈付き ``"ABC"%string`` でよいなら、不要です。


注2 ``String.eqb`` が出現しないのは、ユニフィケーションによって補完されるためです。


ここでは、boolの等式がPropの等式と同値であることの証明を与えて定義しましたが、
``int``型は、nat型の直和型（``nat + nat``）との1対1であることを使って定義します。


# 6. まとめ

MathComp2 (2.0.0) がリリースされましたが、型定義をしない使い方ではあまり影響はありません。
なので、当面は MathComp1 (1.7.x) を使い続けてもよいでしょう。
opam の switch コマンドで切り替えることも可能です。

プロジェクトや勉強会の単位で決めることになります。
ProofCafe -名古屋Coq勉強会 は、MathComp2 に移行します。ELPIの勉強もおこないます。



以上
*)
