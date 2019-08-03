(**
MathComp の subset について
======
2019/05/01

2019/08/03 追記


この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_subset_1.v

 *)

(**
OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)

(**
# はじめに

この小文は、「補題がMathCompに無かったから自分で証明した」というストーリー
だったのですが、その補題は存在する旨の指摘をいただきました。ありがとうございます。
そのため、MathCompの定義とは無関係に自分で証明を試みたものとして、
文言を修正すると同時に、独自の補題であることを示すために、補題名を変更しました。

また、MathComp側の定義についての説明に間違いがあったため、該当箇所の解説も修正しました。

以上の修正については、証明のコードは変更していません。
最後に、MathCompにある補題を使う場合の説明を補足しました。
*)

(**
# 説明

MathComp では、``∈`` を示す `\in` は広く使われるために、``ssrbool.v`` で導入されますが、
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
``\subset`` 演算子が定義されている MathComp の finset.v のコメントには、
実際、そのように記載されています。

``A \subset B == all x \in A satisfy x \in B.`` ..................... (1)


しかし、MathComp の実際の定義は、

``pred0b [predD A & B]`` ............................................ (2)


となっていて、これは、
「論理式 A を満たし、論理式 B を満たさない要素の数が 0 である」という意味です
（predD は difference の意味）。

そこで、(1)と(2)は同値であることを証明してみました。
これは、MathComp の ``fintype.v`` にも類似の補題が証明されているため、
それを使う場合の証明については、補足を参照してください。
*)

(**
# コード例

最初に、通常の Prop 型論理式について同値であることを証明します。

 ``s1 ⊆ s2 <-> ∀x. x ⊆ s1 -> x ⊆ s2``

その後、（MathComp らしく）boolean な論理式について真偽値が一致することを証明します。
*)

From mathcomp Require Import all_ssreflect.

Section Test.
  
  Variable T : finType.

(**
## Prop な論理式での証明
 *)
  
  Lemma mySubsetP (s1 s2 : pred T) :
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

  Lemma mySubsetE (s1 s2 : pred T) :
    s1 \subset s2 = [forall x, (x \in s1) ==> (x \in s2)].
  Proof.
    apply/idP/idP.
    - move=> H.
      apply/forallP => x.
      apply/implyP.
      by apply/mySubsetP : x.

    - move=> H.
      apply/mySubsetP => x.
      move/forallP in H.
      by move: (H x) => {H} /implyP H /=.
  Qed.

(**
# 最初に使った箇所

単一化の証明 http://fetburner.hatenablog.com/entry/2015/12/06/224619

Unify.v を MathComp への移植するときに必要になりました。移植例：

https://github.com/suharahiromichi/coq/blob/master/unify/ssr_unify_bool_3.v
*)

(**
# おまけ

## 直接 boolean の式を証明する
 *)
  
  Lemma mySubsetE' (s1 s2 : pred T) : 
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
  
(**
# 補足

## 補足1 \subsetの定義について

MathComp での \subset の定義と同じものを ``mySubset1`` とします。
*)
  Definition mySubset1 (s1 s2 : pred T) := pred0b [predD s1 & s2].

(**
\subset は simplify タクティクが使えないようにロックされているので、
unlock する必要があります。``rewrite unlock`` すると判ります。
*)

  Goal forall  (s1 s2 : pred T),  s1 \subset s2 = mySubset1 s1 s2.
  Proof.
    move=> s1 s2.
    rewrite unlock /mySubset1.
    done.
  Qed.
  
(**
   predD は差集合を意味して、

``[predD A & B] == difference of collective predicates A and B.``

です。しかし、積集合 ``predI`` と、補集合 ``predC`` を使っても定義できるはずです。
``mySubset2`` に示します。
*)
  Definition mySubset2 (s1 s2 : pred T) := pred0b [predI s1 & [predC s2]].
  
(**
mySubset1 と mySubset2 が同じなのは自明ですが、
それを証明するためには、predI の可換性が必要になります。
その証明には、FunctionalExtension が必要になってしまいました。
*)
  Require Import Coq.Logic.FunctionalExtensionality.
  Goal forall (s1 s2 : pred T), predI s1 s2 = predI s2 s1.
  Proof.
    move=> s1 s2.
    rewrite /predI.
    rewrite /SimplPred.
    f_equal.
    apply: functional_extensionality => x.
      by rewrite Bool.andb_comm.
  Qed.

(**
FunctionalExtension を使わないで済ますために、pred0b までを含めて、
次の補題を証明してみました。あるいは、もっとよい方法があるかもしれません。
 *)
  Lemma predIComm (A B : pred T) : pred0b [predI A & B] = pred0b [predI B & A].
    apply/idP/idP.
    - move/pred0P => H.
      apply/pred0P.
      move=> x.
      move: (H x) => {H} /=.
        by rewrite Bool.andb_comm.
    - move/pred0P => H.
      apply/pred0P.
      move=> x.
      move: (H x) => {H}/=.
        by rewrite Bool.andb_comm.
  Qed.
  
  Goal forall  (s1 s2 : pred T),  mySubset1 s1 s2 = mySubset2 s1 s2.
  Proof.
    move=> s1 s2.
    rewrite /mySubset1 /mySubset2.
    by rewrite predIComm.
  Qed.

(**
## 補足2 MathComp の補題を使う

fintype で定義された subsetP は、リフレクティブ補題ですから、
``apply/`` と ``move/`` で適用します。[1.]の3.7節を参照してください。
*)

  Check @fintype.subsetP : forall (T : finType) (s1 s2 : pred T),
      reflect (forall x, x \in s1 -> x \in s2) (s1 \subset s2).
  
  Lemma mySubsetP' (s1 s2 : pred T) :
    s1 \subset s2 <-> (forall x, x \in s1 -> x \in s2).
  Proof.
    split.
    - by apply/subsetP.                     (* fintype.subsetP *)
    - by move/subsetP.                      (* fintype.subsetP *)
  Qed.

(**
fintype で定義された subsetE は、\subset の定義を展開したものでしかないので、
あまり使いではありません。

そこで、ここでも subsetP を使います。
*)  
  Check @fintype.subsetE : forall (T : finType) (A B : pred T),
      (A \subset B) = pred0b [predD A & B].

  Lemma mySubsetE'' (s1 s2 : pred T) :
    s1 \subset s2 = [forall x, (x \in s1) ==> (x \in s2)].
  Proof.
      by apply/subsetP/forallP => H x; move/implyP: (H x).
  Qed.

(**
これは首記の御指摘のなかで教えていただいたものを使わせていただきました。
重ねて感謝します。
*)
  
End Test.

(**
# 参考文献

[1.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版

*)

(* END *)
