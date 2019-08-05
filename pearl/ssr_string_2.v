(**
MathComp で文字列を使う (スライド版)
======
2019/08/04


- 概要

Coq でプログラムの証明をするとき[3.]など、文字列型を使いたくなります。
MathComp [1.] には文字列の定義がないので、
Starndard Coqの文字列の定義 [2.] を使うことになります。
しかし、Import しただけでは、MathComp の機能を使えません。
文字列型をMathCompの型として使う方法を説明します。わずか1行の定義です。

- この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_string_2.v

 *)

(**
- バージョン


OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)

(**
----------------
# MathComp で自然数型を使う
 *)
From mathcomp Require Import all_ssreflect.

Goal forall (n : nat), (n == 42) || (n != 42).
Proof.
  move=> n.
  case H : (n == 42). (* n が 42 か、そうでないか、で場合分けする。 *)
  - done.             (* n が 42 の場合 *)
  - done.             (* n が 42 でない場合 *)
Qed.

(**
- bool値を返す等式（「==」）が使える。
 *)
Check @eq_op : forall T : eqType, T -> T -> bool. (* 「==」 *)

(**
- bool値を返す等式は、決定性のあるので、
成り立つ場合(true)と、成り立たない場合(false) で場合分けできる。case または destruct。

- 「==」が成り立たなければ、「!=」が成り立つといえる。「!=」は「==」のbool値の否定。
*)



(**
----------------
# MathComp で自然数型を使う（続き）
 *)

Goal forall (n : nat), (n == 42) || (n != 42).
Proof.
  move=> n.
  case: (n == 42).
  - done.                                   (* n == 42 の場合 *)
  - done.                                   (* n != 42 の場合 *)
Qed.

Goal forall (l : seq nat), (l == [:: 42]) || (l != [:: 42]).
Proof.
  move=> l.
  case: (l == [:: 42]).
  - done.                                   (* l == [:: 42] の場合 *)
  - done.                                   (* l != [:: 42] の場合 *)
Qed.

(**
- 自然数型は、決定性のある等式が使える。

- 自然数型を要素とするリストや直積型などでも、決定性のある等式が使える。
*)

(**
---------------
# MathComp で自然数型を使う（続き）
 *)

Check 1      : nat                   : Type.
Check 1      : nat_eqType            : eqType.
Check 1      : Equality.sort nat_eqType.
(* 「==」 *)
Check 1 == 1                : bool.
Check @eq_op nat_eqType 1 1 : bool.
Fail Check @eq_op nat 1 1.

Check [:: 1] : seq nat               : Type.
Check [:: 1] : seq_eqType nat_eqType : eqType.
Check [:: 1] : Equality.sort (seq_eqType nat_eqType).
(* 「==」 *)
Check [:: 1] == [:: 1]                             : bool.
Check @eq_op (seq_eqType nat_eqType) [:: 1] [:: 1] : bool.
Fail Check @eq_op (seq nat) [:: 1] [:: 1].

(**
- nat_eqType は、eqType (決定性のある等式のある型）のインスタンスである。

- 1 は、nat型 であると同時に、nat_eqType型である（と見える）。コアーション。

- 「==」の引数の 1 は、nat_eqType であると対応づけできる。カノニカル・プロジェクション
*)

(**
---------------
# Coq の String型

Starndard Coqのライブラリ ``String.v`` [2.] を使う。
 *)

Require Import String.
Open Scope string_scope.

Check "abc" : string.

(**
- Ascii は bool をコンストラクタで組み立てたもの。
- String は Ascii をコンストラクタで組み立てたもの。
 *)

Import Ascii.
Set Printing All.

Check "A"%char. (* Ascii true false false false false false true false *) (* 41H *)
Check "ABC"%string. (* String "A" (String "B" (String "C" EmptyString)) *)

Unset Printng All.

(**
---------------
# Coq の String型 (続き)

決定性のある等式は、Starndard Coqでも定義されている。ただし、

- 型毎に関数が違う（Notation で、「=?」と定義されてはいる）。
 *)

Goal forall (s1 s2 : string), (String.eqb s1 s2) || (~~ String.eqb s1 s2).
Proof.
  move=> s1 s2.
  case: (String.eqb s1 s2).
  - done.
  - done.
Qed.

(**
- string のリストか可能だが、それに対して「==」が使えない。
*)

Check [:: "ABC"] : seq string.
Fail Check [:: "ABC"] : seq_eqType string.
Fail Check [:: "ABC"] == [:: "ABC"].



(**
---------------
# MathComp で文字列型を使う
 *)

Canonical string_eqType := EqType string (EqMixin String.eqb_spec).

Goal forall (l : string), (l == "ABC") || (l != "ABC").
Proof.
  move=> l.
  case: (l == "ABC").
  - done.                                   (* l == "ABC" の場合 *)
  - done.                                   (* l != "ABC" の場合 *)
Qed.

Goal forall (l : seq string), (l == [:: "ABC"]) || (l != [:: "ABC"]).
Proof.
  move=> l.
  case: (l == [:: "ABC"]).
  - done.                                   (* l == [:: "ABC"] の場合 *)
  - done.                                   (* l != [:: "ABC"] の場合 *)
Qed.


(**
- 文字列型は、決定性のある等式が使える。「==」が使えるようになった。

- 文字列型を要素とするリストや直積型などでも、決定性のある等式が使える、ようになった。
*)


(**
---------------
# MathComp で文字列型を使う（続き）
 *)

Check "ABC"      : string                   : Type.
Check "ABC"      : string_eqType            : eqType.
Check "ABC"      : Equality.sort string_eqType.
(* 「==」 *)
Check "ABC" == "ABC"                   : bool.
Check @eq_op string_eqType "ABC" "ABC" : bool.
Fail Check @eq_op string "ABC" "ABC".


Check [:: "ABC"] : seq string               : Type.
Check [:: "ABC"] : seq_eqType string_eqType : eqType.
Check [:: "ABC"] : Equality.sort (seq_eqType string_eqType).
(* 「==」 *)
Check [:: "ABC"] == [:: "ABC"]                                : bool.
Check @eq_op (seq_eqType string_eqType) [:: "ABC"] [:: "ABC"] : bool.
Fail Check @eq_op (seq string) [:: "ABC"] [:: "ABC"].

(**
- string_eqType は、eqType (決定性のある等式のある型）のインスタンスである、ようになった。

- "ABC" は、string型 であると同時に、string_eqType型である（と見える）、ようにになった。

- 「==」の引数の "ABC" は、string_eqType であると対応づけできる、ようになった。
*)

(**
---------------
# 補足説明 (その1)

Mixin について：
 *)

Check @EqMixin
  : forall (T : Type)                       (* (1) *)
           (op : T -> T -> bool),           (* (2) *)
    (forall x y, reflect (x = y) (op x y))  (* (3) *)
    -> Equality.mixin_of T.

Check @EqMixin nat                          (* (1) *)
      eqn                                   (* (2) *)
      (@eqnP)                               (* (3) *)
  : Equality.mixin_of nat.

Check @EqMixin (seq nat)
      eqseq
      (@eqseqP nat_eqType)
  : Equality.mixin_of (seq nat).

Check @EqMixin string                       (* (1) *)
      String.eqb                            (* (2) *)
      String.eqb_spec                       (* (3) *)
  : Equality.mixin_of string.

Check @EqMixin (seq string)
      eqseq
      (@eqseqP string_eqType)
  : Equality.mixin_of (seq string).

(**
(1) ベースとなる型、ここでは string

(2) 決定性のある、bool型を返す等式。

(3) (2)が、「=」と同値であることの証明を与える。ただし、bool型のtrueなら証明可能とみなす。

String型については、(1)(2)(3)とも、String.v で定義されてりるので、それを使う。

より詳しい説明は、[4.][5.]。
  *)

(**
---------------
# 補足説明 (その2)

String.v での定義について：
*)

(**
(2) bool値を返す等式の定義
 *)

Print String.eqb.
(**
```

Fixpoint eqb s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' =>
     if (Ascii.eqb c1 c2) then (eqb s1' s2') else false
 | _,_ => false
 end.

```

*)

(**
(3) の証明、リフレクティブ補題 ([4.])
*)

Check String.eqb_spec
  : forall s1 s2 : string, reflect (s1 = s2) (String.eqb s1 s2).


(**
---------------
# 文献

[1.] Mathematical Components 公式

https://math-comp.github.io/


[2.] Library Coq.Strings.String

https://coq.inria.fr/library/Coq.Strings.String.html


[3.] 「The Little Prover」のCoqでの実現---「定理証明手習い」の「公理」をCoqで証明してみた

https://qiita.com/suharahiromichi/items/723896ebfbc332f9d3dd


[4.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版


[5.] Mathematical Components Book

https://math-comp.github.io/mcb/

 *)

(* END *)
