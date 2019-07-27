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

たとえばプログラムの証明をCoq/SSReflect/MathCompでおこなうとき、
プログラムに文字列をデータとして使いたい場合があります。

Mathcompのライブラリには文字列がないため、Standard Coqの String型 を使うことになります。

さらに、Mathcomp に含まれる 決定性のある等式 (decidable equality) の型クラス
である eqType のインスタンスとすることで、
Mathcomp の bool値を返す等号演算子「==」を使って、
natやseq (list) などの他のデータ型と同様に、
bool値の等式が使えるようになります。
*)

(**
# コード例

コード例を以下に示します。(1)と(2)はライブラリのインクルードなので、
実質は、(3)と(4)の2行です。
*)

From mathcomp Require Import all_ssreflect. (* (1) *)
Require Import String.                      (* (2) *)

Definition string_eqMixin := @EqMixin string String.eqb String.eqb_spec. (* (3) *)
Canonical string_eqType := EqType string string_eqMixin. (* (4) *)

(**
(3) は、つぎのふたつから、Mixinをつくります。

- String.eqb、String型の決定性のある（bool値を返す）等式の関数
- String.eqb_spec、Coqの通常の等式（Prop型の等式、ライプニッツの等式）と、
String.eqb（bool値の等式）が同値であることを示す補題


後者はリフレクション補題と呼ばれるものです。Prop型とbool値では型が違うわけですが、
``is_true b := (b = true)`` という関数を補って、bool値をProp型にして考えます
（これをコアーションといいます）。

リフレクション補題は、通常、それぞれにの型ごとに証明をする必要がありますが、
今回String型については、Standard Coqのライブラリで証明されていたものを使っています。
(Standard CoqがMathCompに歩み寄った、ということでしょうか。）

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
## リフレクションを含む証明の例

詳しい説明は省きますが、move/eqP と apply/eqP が、
Propの等式とbool値の等式のリフレクションをおこなうタクティクです。
なお、これは説明のために冗長な書き方になっています。
*)

Goal forall X : string, if X != "abc" then X <> "abc" else X = "abc".
Proof.
  move=> X.
  case: ifP.
  - move=> H; by apply/eqP.
  - by move/eqP.
Qed.

(**
# まとめ

Mathcomp で文字列を使う方法をのべました。実質2行なので、ぜひお試しください。
これを応用した証明の例として、以下も合わせて読んでいただけると幸いです。

「The Little Prover」のCoqでの実現---「定理証明手習い」の「公理」をCoqで証明してみた

https://qiita.com/suharahiromichi/items/723896ebfbc332f9d3dd
 *)

(* END *)
