(**
MathComp で文字列を使う
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

MathCompのライブラリには文字列がないため、
Standard Coqの String型 ([2.]) を使うことになります。

一方、自然数(nat型)などのMathCompで使うデータ型は、
eqTypeという、決定性のある等式 (decidable equality) の型クラス
のインスタンスとしても定義されています(nat型に対してnat_eqType型、[3.])。

これによって、（MathCompらしく）bool値を返す等号演算子「==」を使ったり、
MathCompの等式についての補題が使えるようになっています。

ここでは、あらたな型(string_eqType型)を定義することで、
文字列をMathCompらしく使えるようにしたいとおもいます。
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
string_eqType を構成する EqTypeの構造体のsortフィールドに、string型が格納されます。
 *)

Compute @Equality.sort string_eqType.       (* string. *)

(**
さらに、Definition ではなく、Canonical を使うことで、
string_eqType が  string に、対応づけ(Canonical Projection)されます。
これにより、string型の値をstring_eqType型とみなして処理をすることができるようになります。
（後述）。
 *)

Open Scope string_scope.                    (* (5) *)

(**
(5)はダブルクォーテーションで挟んだ部分を文字列とする宣言です。その代わりに、
``"abc"%string`` と「%」の後ろに型を明示（アノテーション）してもよいです。
*)

(**
# string_eqType型を定義すると、なにがうれしいか

以上で、string_eqType型を定義し、
string型に対してbool型の等号「==」が使えるようになりました。
これでなにがうれしいのでしょうか。ここでできるのは以下のことです。

- string型の値どうしが、等しいことが証明できる。また、等しくないことが証明できる。
（これは、Prop型の等号「=」でも証明できる）

- string型の値どうしが、等しいか等しくないか、で場合わけできる。
（これは、String.string_dec (standard coq の sumbool) でも可能である）

- ひとたび bool値の false/true が決まれば、
bool値の計算によって証明を進めることができる。
（これは、String.eqb だけでも可能である）


これらに加えて、

1. bool値の等号「==」が使える。

2. eqType に関する補題がつかえるようになる。

3. 直積型(prod型)や、リスト型(seq型)などの中で使った場合、
それに対して、1.〜2. のことが可能になる。

自然数nat型に対しても、nat_eqType が定義されているため、1.〜3.が可能になっています。
これと同じことがstring型についても行えるようになったわけです。
 *)

(**
# Canonical宣言の補足説明

## ここまでで、なにが起きているか

(6)が成り立つようになります。
 *)

Check "abc" : string        : Type.
Check "abc" : string_eqType : eqType.       (* (6) *)

(**
これをもって、「string型の値をstring_eqType型とみなす」といっても構わないわけですが。。。

(6)をコアーションを省略せずに書くと次のようになります。
EqualityはeqTypeの正式なModule名です。
 *)
Check "abc" : Equality.sort string_eqType.

(**
Coqといえど、特定の値が複数種類の型を持つことができるわけではなく、
string_eqType型を定義する eqType の構造体の sort フィールドに格納された
string型への参照を取り出しているわけで、
取り出すためのキーが省略されているだけです。
*)

(**
## 演算子「==」について

演算子「==」は、関数eq_opのNotation （構文糖衣）です。
関数としてのeq_opは、本来ならば3引数なのですが、
通常、その第1引数である型の指定を省略します（省略しなければならない）。
*)

Check "abc" == "abc" : bool.                (* (7) *)
Check eq_op : _ -> _ -> bool.
Check eq_op "abc" "abc" : bool.

(**
そこで、「@」を使って、引数を省略せずに指定すると次のようになります。
 *)
Check @eq_op : forall T : eqType, T -> T -> bool.
Check @eq_op string_eqType "abc" "abc".

(**
eq_op は、「eqType型の型の値」をとる関数ですから、
引数の型は string_eqType型 でなければなりません。
 *)

(**

しかしながら、``"abc" == "abc"`` あるいは ``eq_op "abc" "abc"`` とした場合、
eq_op は、自分が"はstring型の引数を取っているは判っても、
それから string_eqType を対応付けすることができません。

(6)の場合は、string_eqType が書かれるべきと判っていたので、
string型が与えれてもコアーションで補うことができました。
しかし、(7)はeqTypeのインスタンスならなんでもよいので、
string型が与えれてもstring_eqType型に対応づけることができません。
（これは、1からnat型を対応できますが、nat型からかならずしも1を対応できないのと同じことです）
それで、そのことをCoqの処理系に教えておいてあげるわけです。
これを、

string_eqType型 は sring型 の sort についての Canonical Solution である

といいます。

Canonical 宣言によって、string から string_eqType への対応付け（Canonical Projection）
を登録することで、
そのことを教えてあげるわけです。そのProjectionは次のコマンドで確認することができます。
*)

Print Canonical Projections.

(* string <- Equality.sort ( string_eqType ) *)

(**
繰り返しになりますが、

string_eqType → string の対応関係は、string_eqType 内部に保持されるのに対して、
string → string_eqType の対応関係は、Coqの処理系のデータベースに保持されます。

あとは、コアーションでうまく処理されます。
 *)

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

eqType型で定義された補題pair_eqPを使ってみた例です。
 *)

Goal forall x y : string,
    x == "abc" -> y == "xyz" -> (x, y) == ("abc", "xyz").
Proof.
  move=> x y Hx Hy.
  apply/eqP/pair_eqP/andP.
    by split => /=.
Qed.  

(**
string型どうしからなる直積型 ``string * string``型
の ``(x, y) == ("abc", "xyz")``
を ``x == "abc" /\ y == "xyz"`` に変形して証明する例です。

実は、``string * string`` 型ではなく、``prod_eqType string_eqType string_eqType``型
になっている（Canonical Projection）ことに注意してください。
string型に 「==」 ができないのと同様に、``string * string``型にも、
「==」 を適用できません。

eqType型に使える補題については [6.]の4.2節を参照してください。
*)

(**
# まとめ

MathComp で文字列を使う方法をのべました。実質2行なので、ぜひお試しください。

これを使って Lisp のプログラムを証明した例が[1.]です。あわせてご覧ください。

コアーションについてのもうすこし詳しい説明は[4.]にあります。これもあわせてご覧ください。

MathComp の公式サイトは[0.]です。
解説書は [5.] です。入門から内部構造まで広くカバーしています。
5.3節に詳しい説明があります。
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
