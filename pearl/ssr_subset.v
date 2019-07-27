(**
Mathcomp の subset について
======
2019/05/01


この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_subset.v

 *)

(**
OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)

(**
# 説明

Mathcomp では、``∈`` を示す `\in` は広く使われるために、``ssrbool.v`` で導入されますが、
部分集合 ``⊆`` を示す、``\subset`` は、fintype.v で導入されています。

要素がすべて列挙できる有限型 ``T : finType`` の上で、そのT の enumを全集合とすることで、
ひと通りの集合演算が定義できるようになるからです。

``T : finType`` のとき、booleanな関数 ``P : T -> bool`` を集合と同一視して、
``P x`` を ``x \in P`` と同一視します。


すると、その上で、集合 A と B の積を
``x ∈ A ∩ B`` <-> `` (λx. A x ∧ B x) x`` 

P の補集合を
``x ∈ P^c`` <-> `` (λx. ¬ P x)`` 

と定義できます。

T の enum に対してPでフィルタすることで、Pの要素がすべて求められるので、
その数を数えるとPの濃度を求めることができます。


表記法 Notation については、文献[1.]の表5.1などを参照してください。


また、``P : T -> bool`` を ``P : pred T`` と書くこともありますが、
これは表記のみの違いです。


さて、ここからが本題です。


集合Aが集合Bの部分集合 ``A ⊆ B`` であるとは、A の任意の要素が B の要素であることです。
``\subset`` 演算子が定義されている Mathcomp の finset.v のコメントには、
実際、そのように記載されています。

``A \subset B == all x \in A satisfy x \in B.`` ..................... (1)


しかし、Mathcomp の実際の定義は、

``pred0b [predI A & [predC B]]`` .................................... (2)


となっていて、これは、
「論理式 A を満たし、論理式 B を満たさない要素の数が 0 である」という意味です。

(1)と(2)は同値のはずですが、それを証明する補題がなかった（見つけられなかった）ので、
証明してみました。

*)

(**
# コード例

最初に、通常の Prop 型論理式について同値であることを証明します。

 ``s1 ⊆ s2 <-> ∀x. x ⊆ s1 -> x ⊆ s2``

その後、（Mathcomp らしく）boolean な論理式について真偽値が一致することを証明します。
*)

From mathcomp Require Import all_ssreflect.

Section Test.
  
  Variable T : finType.

(**
## Prop な論理式での証明
 *)
  
  Lemma subsetP (s1 s2 : pred T) :
    s1 \subset s2 <-> (forall x, x \in s1 -> x \in s2).
  Proof.
    rewrite subset_disjoint /disjoint.
    split.
    - move/pred0P => H.
      move=> x Hs1.
      move: (H x) => {H} /= /eqP.
      rewrite inE eqbF_neg negb_and /=.
      move/orP => [Hn1 | Hnn2].
      + by move/negP : Hn1.
      + by rewrite Bool.negb_involutive in Hnn2.

    - move=> H.
      apply/pred0P => x.
      apply/andP => [[H1 Hn2]].
      rewrite inE /= in Hn2.
      move/negP in Hn2.
        by apply/Hn2/H.
  Qed.
  
(**
## boolean な論理式での証明
 *)

  Lemma subsetE (s1 s2 : pred T) :
    s1 \subset s2 = [forall x, (x \in s1) ==> (x \in s2)].
  Proof.
    apply/idP/idP.
    - move=> H.
      apply/forallP => x.
      apply/implyP.
      by apply/subsetP : x.

    - move=> H.
      apply/subsetP => x.
      move/forallP in H.
      by move: (H x) => {H} /implyP H /=.
  Qed.

(**
# 最初に使った箇所

単一化の証明 http://fetburner.hatenablog.com/entry/2015/12/06/224619

Unify.v を Mathcomp への移植するときに必要になりました。移植例：

https://github.com/suharahiromichi/coq/blob/master/unify/ssr_unify_bool_3.v
*)

(**
# おまけ

## 直接 boolean の式を証明する
 *)
  
  Lemma subsetE' (s1 s2 : pred T) : 
    s1 \subset s2 = [forall x, (x \in s1) ==> (x \in s2)].
  Proof.
    rewrite subset_disjoint /disjoint.
    apply/idP/idP.
    - move/pred0P => H.
      apply/forallP => x.
      apply/implyP => Hs1.
      move: (H x) => {H} /= /eqP.
      rewrite inE eqbF_neg negb_and /=.
      move/orP => [Hn1 | Hnn2].
      + by move/negP : Hn1.
      + by rewrite Bool.negb_involutive in Hnn2.
        
    - move/forallP => H.
      apply/pred0P => x.
      move: (H x) => {H} /implyP H /=.
      apply/andP => [[H1 Hn2]].
      rewrite inE /= in Hn2.
      move/negP in Hn2.
        by apply/Hn2/H.
  Qed.
  
End Test.

(**
# 参考文献

[1.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版

*)

(* END *)
