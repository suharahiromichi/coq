(**
MathComp で文字列を使う (MathComp2版)
==============================
2023/05/18


@suharahiromichi


- 概要

Coq でプログラムの証明をするときなど、文字列型を使いたくなります。
MathComp [1.] には文字列の定義がないので、
Starndard Coqの文字列の定義 [2.] を使うことになります。
しかし、Import しただけでは、MathComp の機能を使えません。
文字列型をMathCompの型として使う方法を説明します。わずか1行の定義です。

MathComp 1.x系列 (以下MathComp1) から MathComp 2.0.0 (以下MathComp2) への変更で、
Hierarchy Builder (HB) を使って定義するように変更され、そのインポートが必要になり
ましたが、1行で定義できることには違いがありません。

MathComp2では、eqType型のインスタンスとしての stirng_eqType型などが廃止され、
string型がeqType型のインスタンスになるよう単純化されました。
しかし、通常の証明では、このこととを意識することは少なく、互換性は維持されているといえます。

- この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/ssr2/ssr2_string.v



- 比較のために、MathComp1 のコードを示します。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_string_3.v
 *)

(**
- バージョン


OCaml 4.14.1, Coq 8.17.0, MathComp 2.0.0, Hierarchy Builder 1.4.0 
 *)

(**
---------------
# MathComp2 での定義
 *)

From HB Require Import structures.          (* MathComp2 *)
From mathcomp Require Import all_ssreflect.
Require Import String.
Open Scope string_scope.

Print hasDecEq.Build.
Print Equality.Mixin.
Print hasDecEq.phant_Build.
Print Equality.axiom.
Print eq_axiom.
Check @hasDecEq.Build string String.eqb String.eqb_spec.

HB.instance Definition _ := hasDecEq.Build string String.eqb_spec. (* MathComp2 *)

(**
---------------
# MathComp で文字列型を使う
 *)

(**
これは証明できない。
 *)
Goal forall (l : string), l = "ABC" \/ l <> "ABC".
Proof.
  move=> l.
  Search _ (_ \/ _).
  Check @orP.
  Fail apply/orP.
Admitted.

(**
bool の等式にすると証明できる。
 *)
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

Check "ABC"      : string        : Type.
Fail Check "ABC" : string_eqType : eqType.      (* MathComp1 *)
Fail Check "ABC" : Equality.sort string_eqType. (* MathComp1 *)
Check "ABC"      : string        : eqType.      (* MathComp2 *)

(* 「==」 *)
Check "ABC" == "ABC"                        : bool.
Fail Check @eq_op string_eqType "ABC" "ABC" : bool. (* MathComp1 *)
Check      @eq_op string        "ABC" "ABC" : bool. (* MathComp2 *)

Check [:: "ABC"]      : seq string               : Type.
Fail Check [:: "ABC"] : seq_eqType string_eqType : eqType. (* MathComp1 *)
Check [:: "ABC"]      : seq string               : eqType. (* MathComp2 *)

(**
- string は、eqType (決定性のある等式のある型）のインスタンスである、ようになった。

MathComp1 では、string_eqType は eqType のインスタンスであり、"ABC"はstring型であると同時に
コアーションによって、``"ABC" : string_eqType`` が成立していたが、MathComp2では単純になった。

- 「==」の引数の "ABC" は、string であると対応づけできる、ようになった。
*)

(**
---------------
# 補足説明

Standard Coq の String.v での定義と証明済みの補題について：
*)

(**
- bool値を返す決定性のある等式の定義
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
- リフレクティブ補題

String.eqbが「=」と同値であることの証明を与える。
ただし、bool型のtrueなら証明可能とみなす。
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



[3.] Hierarchy Builder

https://github.com/math-comp/hierarchy-builder
 *)

(* END *)
