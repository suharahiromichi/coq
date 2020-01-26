(**
MathComp における古典論理
======
2020/01/25


この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_classically.v

 *)

(**
OCaml 4.07.1, Coq 8.9.1, MathComp 1.9.0
 *)

From mathcomp Require Import all_ssreflect.

(**
----------------
# MathComp は排中律を仮定しているのか

Stackoverflow (英語版）に、こんな質問がありました([1.])。

``forall A: Prop, A \/ ~A``


の証明を教えてほしいという趣旨です。クローズしているようなのですが、
その回答にあるように、MathComp のライブラリには排中律の公理が定義されていないので、
任意の ``A : Prop`` については証明できません。

排中律の公理を自分で定義するか、
Standard CoqのClassical.vを導入すればよいのですが、
そもそも MathComp のライブラリには公理、すなわち、証明なしで導入される
命題は含まれていないのです。

このことは [2.] の3.3節に説明があって、


The Mathematical Components library is axiom free. This makes the
library compatible with any combination of axioms that is known to be
consistent with the Calculus of Inductive Constructions.


要するに（Standard Coqと違って）、
CICとの互換性が保たれない（かもしれない）命題は一切入れないのだ、
ということのようです（注1）。これを "axiom free" というのだそうです。

では、排中律ががなくて困ることはないのでしょうか？

結論からいうと、ある命題が同値なbool値の式に変換（リフレクト）できるならば（注2)、
その命題は真か偽の決まる（注3）という決定性があることになり、
排中律や二重否定除去が定理として証明できるはずです。
なので、公理として排中律を導入する必要はないわけです。

（注1）実際には、MathComp のライブラリの中で Axiom コマンドは使われています。

（注2) bool型の式は、計算すればtrueかfalseに値が決まる決定性を持つため。

（注3) 正確には、真であると証明できるか、その否定が証明できる、というべき。
 *)

(**
----------------
# Standard Coq の場合

Standard Coq では Classical.v で次のように定義されています。
 *)
Require Import Classical.
(**
まず、排中律(classic)が公理として定義され、
 *)
Check classic : forall P : Prop, P \/ ~ P.  (* 排中律 *)

(**
それから二重否定除去(NNPP)が証明されています。
 *)
Lemma NNPP : forall P : Prop, ~ ~ P -> P.   (* 二重否定除去 *)
Proof.
  intro P.
  now case (classic P).
Qed.

(**
----------------
# MathComp の場合

## 一般の命題 P

MathComp では、Prop型の命題 P が bool型の式 b にリフレクトできる（注4）
ことを ``reflect P b`` で表します。``reflect P b`` が成り立っていることを前提として
（公理とするわけではない）、排中律を導いてみましょう。

（注4） b を ``b = true`` というProp型の命題と解釈したときに、それがPと同値である。
*)

(**
命題Pにリフレクトできるブール型の式bがあるなら、命題Pは排中律は成り立つ。

証明自体は単純で、b を true と false で場合分け(case)したのち、
true ならゴールの選言のleftをとり、bool値にリフレクトするとtrue。
false ならゴールの選言のrightをとり、bool値にリフレクトすると~~ false。
になります。bool値falseの否定はtrueに決まっているので、どちらも真になります。
 *)

Lemma ssr_em_p (P : Prop) (b : bool) : reflect P b -> P \/ ~ P.
Proof.
  case: b => Hr.
  - left.
    apply/Hr.
    done.
  - right.
    apply/Hr.
    done.

    Restart.
    
    by case: b => Hr; [left | right]; apply/Hr.
Qed.

(**
Staandard Coq の場合と同様に、排中律から二重否定除去は証明できます。
 *)
Lemma ssr_nnpp_p (P : Prop) (b : bool) : reflect P b -> ~ ~ P -> P.
  move=> Hr.
    by case: (ssr_em_p P b Hr).
Qed.

(**
[2.] の3.3節では、

```
Definition classically P := forall b : bool, (P -> b) -> b
```

を導入していくつかの補題を証明していますが、classically の「見た目」から判るように
これはモナディックな定義です。今回はそれを使いません。
モナデックな方法ついては稿を改めて説明したいとおもいます。
*)

(**
## 具体的な P (自然数の等式の例)

では、命題Pにリフレクトできるブール式bがあるような命題Pとはなんでしょうか。

自然数どうしの等式がこれにあたります。
*)

(**
MathComp では、このような決定性のある等式の成り立つ型を eqType といいます。
nat は eqType ですので（注5）、これが成り立ちます。

（注5）eqType のインスタンス nat_eqType が nat の正準型（カノニカル）であるという。
*)

(**
自然数の等式の命題 m = n は、bool型の式 m == n にリフレクトできます。
具体的には、次の補題 eqP が MathComp のなかで定義されています。
*)

Check @eqP nat_eqType : forall (m n : nat), reflect (m = n) (m == n).

(**
eqP を使うと、自然数の等式の命題の排中律と二重否定除去が証明できます。
*)

Lemma ssr_em_eq (m n : nat) : m = n \/ m <> n.
Proof.
  apply: ssr_em_p.
    by apply: eqP.
Qed.

Lemma ssr_nnpp_eq (m n : nat) : ~ m <> n -> m = n.
Proof.
  apply: ssr_nnpp_p.
    by apply: eqP.
Qed.

(**
# まとめ

実際、ふたつの自然数m と n の等式 m = n は、成立するかしないかのどちらかで、決定性
があります。また、 m <> n の否定は m = n でよいはずです。

MathComp はこのように、Coqのうえで普通の「数学」をするための仕組みなわけです。
*)

(**
---------------
# 文献

[1.] Does ssreflect assume excluded middle?

https://stackoverflow.com/questions/34520944/does-ssreflect-assume-excluded-middle


[2.] Mathematical Components Book

https://math-comp.github.io/mcb/

 *)

(* END *)
