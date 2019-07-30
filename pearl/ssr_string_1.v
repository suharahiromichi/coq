(**
Mathcomp で文字列を使う (スライド版)
======
2019/07/24


この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_string_1.v

 *)

(**
OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)


(**
# Mathcomp の証明の例
 *)
From mathcomp Require Import all_ssreflect. (* (1) *)

Lemma nat_eq_noteq (m n : nat) : (m == n) || (m != n).
Proof.
  case: (m == n).     (* destruct (m == n) でもおなじ。 *)
  - done.             (* m == n が成り立つ。 *)
  - done.             (* m == n が成り立たない。m != n が成り立つ。 *)
Qed.

(**
``case: (m == n)`` で、``m == n`` が成り立つ場合と、
成り立たない場合に場合分けする。

Mathcomp では自然数について、
かならず真偽どちらかに決まる、
決定性のある等式「==」が定義されている。

Standard Coqでは定義されていない。通常sumboolを使う。
Software FoundationsではBasic.vで定義されている。beq_nat。
*)


(**
# Mathcomp の型クラス構造（自然数）
 *)

Check 1 : nat_eqType : eqType : Type.
Check 1 : nat        : Type.

(**
```
        nat_eqType ← eqType
         V            ↑
1    ← nat        ← Type


← : 型の要素の関係
＜ : 型
```
 *)

(**
ただし、1 : nat_eqType の部分は、sort の呼び出しが省略されたもの。
*)
Compute Equality.sort nat_eqType.       (* nat *)
Check 1 : Equality.sort nat_eqType.


(**
# Mathcomp の型クラス構造（自然数のリスト）
 *)

Check [:: 1] : seq_eqType nat_eqType : eqType : Type.
Check [:: 1] : seq        nat        : Type.

(**
```
         seq_eqType nat_eqType ← eqType
          V                        ↑
[:: 1]← seq  nat               ← Type


← : 型の要素の関係
＜ : 型
```
 *)

Compute Equality.sort (seq_eqType nat_eqType). (* seq nat *)
Check [:: 1] : Equality.sort (seq_eqType nat_eqType).


(**
# String型

Starndard Coqのライブラリを使う。
 *)

Require Import String.                      (* (2) *)

Check "abc"%string : string.

Open Scope string_scope.

Check "abc" : string.

(**
- Ascii は bool をコンストラクタで組み立てたもの。
- String は Ascii をコンストラクタで組み立てたもの。

"abc" =
String (Ascii.Ascii true false false false false true true false)
       (String (Ascii.Ascii false true false false false true true false)
               (String (Ascii.Ascii true true false false false true true false)
                       EmptyString))
*)

(**
実は、Ascii型とString型については、Starndard Coq側にも決定性のある等式が定義されている。
*)


(**
# String を Mathcomp のクラス構造に組み込む

 *)

Definition string_eqMixin := @EqMixin string String.eqb String.eqb_spec. (* (3) *)
Canonical string_eqType := EqType string string_eqMixin. (* (4) *)


(**
# Mathcomp の型クラス構造（文字列）
 *)

Check "abc" : string_eqType : eqType : Type.
Check "abc" : string        : Type.

(**
```
         string_eqType ← eqType
          V            ↑
"abc" ← string        ← Type


← : 型の要素の関係
＜ : 型
```
 *)

(**
ただし、"abc" : string_eqType の部分は、sort の呼び出しが省略されたもの。
*)
Compute Equality.sort string_eqType.       (* string *)
Check "abc" : Equality.sort string_eqType.


(**
# Mathcomp の型クラス構造（リスト）
 *)

Check [:: "abc"] : seq_eqType string_eqType : eqType : Type.
Check [:: "abc"] : seq        string        : Type.

(**
```
         seq_eqType string_eqType ← eqType
          V                        ↑
[:: 1]← seq  string               ← Type


← : 型の要素の関係
＜ : 型
```
 *)


(**
# まとめ
 *)

From mathcomp Require Import all_ssreflect. (* (1) *)
Require Import String.                      (* (2) *)

Definition string_eqMixin := @EqMixin string String.eqb String.eqb_spec. (* (3) *)
Canonical string_eqType := EqType string string_eqMixin. (* (4) *)

(**
1. 決定性のある bool値 の等号「==」が使える。

2. eqType に関する補題がつかえるようになる。

3. 直積型(prod型)や、リスト型(seq型)などの中で使った場合、
それに対して、1.〜2. のことが可能になる。

*)

(**
# 文献

[0.] Mathematical Components 公式

https://math-comp.github.io/


[1.] 「The Little Prover」のCoqでの実現---「定理証明手習い」の「公理」をCoqで証明してみた

https://qiita.com/suharahiromichi/items/723896ebfbc332f9d3dd


[2.] Library Coq.Strings.String

https://coq.inria.fr/library/Coq.Strings.String.html


[3.] Library mathcomp.ssreflect.eqtype

https://math-comp.github.io/htmldoc/mathcomp.ssreflect.eqtype.html


[4.] リフレクションのしくみをつくる

https://qiita.com/suharahiromichi/items/9cd109386278b4a22a63


[5.] Mathematical Components Book

https://math-comp.github.io/mcb/


[6.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版

 *)

(* END *)
