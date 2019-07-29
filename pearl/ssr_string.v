(**
Mathcomp で文字列を使う
======
2019/07/24


この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_string.v

 *)

(**
OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)

(**
# 説明

プログラムの証明をCoq/SSReflect/MathCompでおこなうとき、
プログラムに文字列をデータとして使いたい場合があります（[1.]）。

Mathcompのライブラリには文字列がないため、
Standard Coqの String型 ([2.]) を使うことになります。

さらに、Mathcomp に含まれる eqType ([3.]) という
決定性のある等式 (decidable equality) の型クラス
のインスタンスとすることで、
（Mathcompらしく）bool値を返す等号演算子「==」を使ったり、
Mathcompん等式についての補題が使えるようになります。
*)

(**
# コード例

コード例を以下に示します。(1)と(2)はライブラリのインクルードです。
*)

From mathcomp Require Import all_ssreflect. (* (1) *)
Require Import String.                      (* (2) *)

(**
実質は、次の(3)と(4)の2行です。
*)

Definition string_eqMixin := @EqMixin string String.eqb String.eqb_spec. (* (3) *)
Canonical string_eqType := EqType string string_eqMixin. (* (4) *)

(**
(3) は、つぎのふたつから、Mixinをつくります。

- String.eqb ... String型の決定性のある（bool値を返す）等式の関数
- String.eqb_spec ... Coqの通常の等式（Prop型の等式、ライプニッツの等式）と、
String.eqb（bool値の等式）が同値であることを示す補題


どちらも[2.]の中で定義されているのを使います。

String.eqb は ふたつのstring型の値が、等しいならtrue、等しくないかfalse返す関数です。
この関数は停止して、
かならずどちらの値を返すという「決定性」をもっていることに注意してください。
後述しますが、bool値を返す等号演算子「==」の実体はこの関数になります。

String.eqb_specはリフレクション補題と呼ばれるものです。
Prop型とbool値では型が違うわけですが、``is_true b := (b = true)``
という関数を補って、bool値をProp型にして考えます
（これをコアーションといいます）。

(4) は、(3)のMixinから、``eqType``のインスタンスである``string_eqType``を生成します。
このとき、Definition ではなく、Canonical を使うことで、
string_eqType を (sortにおける）string の正準解になります。
sort は、eqType の構造体において、型stringが格納されるフィールドの名前です。
 *)

Open Scope string_scope.                    (* (5) *)

(**
(5)はダブルクォーテーションで挟んだ部分を文字列とする宣言です。その代わりに、
``"abc"%string`` と「%」の後ろに型を明示（アノテーション）してもよいです。
*)

(**
# string_eqType でなにがうれしいか

以上で、string_eqType を定義し、
string型に対してbool型の等号「==」が使えるようになりました。
これでなにがうれしいのでしょうか。ここでできるのは以下のことです。

1. string型の値どうしが、等しいことが証明できる。また、等しくないことが証明できる。
（これは、Prop型の等号「=」でも証明できる）

2. string型の値どうしが、等しいか等しくないか、で場合わけできる。
（これは、String.string_dec (standard coq の sumbool) でも可能である）

3. ひとたび bool値の false/true が決まれば、
bool値の計算によって証明を進めることができる。
（これは、String.eqb だけでも可能である）

これらに加えて、

4. Mathcomp のnat型のように、bool値の等号「==」が使える。

5. Mathcomp のnat型のように、eqType に関する補題がつかえるようになる。

6. Mathcomp のnat型のように、pair型 や seq型（リスト）の中で使った場合、
それに対して、1.〜5. のことが可能になる。
 *)



(**
# Canonical宣言の補足説明

演算子「==」は、関数eq_opのNotation （構文糖衣）です。
関数としてのeq_opは、本来ならば3引数なのですが、
通常、その第1引数である型の指定を省略します（省略しなければならない）。
*)
Check "abc" == "abc" : bool.
Check eq_op : _ -> _ -> bool.
Check eq_op "abc" "abc" : bool.

(**
そこで、「@」を使って、引数を省略せずに指定すると次のようになります。
 *)
Check @eq_op : forall T : eqType, T -> T -> bool.
Check @eq_op string_eqType "abc" "abc".

(**
eq_op は、eqType型で定義された関数ですから、型の指定は string_eqType とする必要があります。
しかしながら、``"abc" == "abc"`` あるいは ``eq_op "abc" "abc"`` とした場合、
eq_op は、自分が"はstring型の引数をとっていることは判っても、
それから string_eqType を対応付けすることができません。
（逆に、string_eqType から string を対応付けすることはできます。
eqType構造体を調べればそのsortフィールドに string型 が格納されているからです。）

Canonical 宣言によって、string から string_eqType への対応付け（Projection）
を登録することで、
そのことを教えてあげるわけです。そのProjectionは次のコマンドで確認することができます。
*)

Print Canonical Projections.

(* string <- Equality.sort ( string_eqType ) *)

(**
# テストコード
 *)

(**
## true または false の決定
*)

(**
bool値の演算子「==」の等式は、計算によって真偽が決まります。
 *)
Compute "abc" == "abc".                     (* true *)
Compute "abc" == "abcd".                    (* false *)

(**
これに対して、Prop型の演算子「=」の等式は、変化がありません。
*)
Compute "abc" = "abc".                      (* "abc" = "abc" *)
Compute "abc" = "abcd".                     (* "abc" = "abcd" *)

(**
## bool値の計算による証明の例
*)

Goal ("abc" == "abc") && ("xyz" == "xyz") || ("abc" == "abcd") .
Proof.
  done.
Qed.

(**
bool値の等式の場合、ひとたびfalseまたはtrueが決まれば、
どんな複雑な式であっても、bool値の計算で全体の真偽を求めることができます。

これに対して、Prop型の等式に場合は、連言と選言を分解して証明する必要があります。
*)

Goal "abc" = "abc" /\ "xyz" = "xyz" \/ "abc" = "abcd".
Proof.
  left.
  split.
  - reflexivity.
  - reflexivity.
Qed.

(**
## 証明の例

string型どうしからなるPair型 ``string * string`` の ``(x, y) == ("abc", "xyz")``
を ``x == "abc" /\ y == "xyz"`` に変形して証明する例です。

本来 ``string * string`` 型には 「==」は適用できず、
実は、``string_eqType * string_eqType`` になっていることの注意してください。
また、pair_eqP は eqType型についての補題です。

eqType 型に使える補題については [4.] も参照してください。
*)

Goal forall x y : string,
    x == "abc" -> y == "xyz" -> (x, y) == ("abc", "xyz").
Proof.
  move=> x y Hx Hy.
  apply/eqP/pair_eqP/andP.
    by split => /=.
Qed.  

(**
# まとめ

Mathcomp で文字列を使う方法をのべました。実質2行なので、ぜひお試しください。

これを使って Lisp のプログラムを証明した例が[1.]です。あわせてご覧ください。

# 文献

[1.] 「The Little Prover」のCoqでの実現---「定理証明手習い」の「公理」をCoqで証明してみた

https://qiita.com/suharahiromichi/items/723896ebfbc332f9d3dd


[2.] Library Coq.Strings.String

https://coq.inria.fr/library/Coq.Strings.String.html


[3.] Library mathcomp.ssreflect.eqtype

https://math-comp.github.io/htmldoc/mathcomp.ssreflect.eqtype.html


[4.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版
 *)

(* END *)
