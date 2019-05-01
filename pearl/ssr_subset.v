(**
Mathcomp の subset について
======
2019/05/01

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_subset.v

 *)

(**

# はじめに

集合Aが集合Bの部分集合 ``A ⊆ B`` であるとは、A の任意の要素が B の要素であることです。
``\subset`` 演算子が定義されている Mathcomp の finset.v のコメントには、
そのように記載されています。

``A \subset B == all x \in A satisfy x \in B.`` ..................... (1)


しかし、Mathcomp の実際の定義は、

``pred0b [predI A & [predC B]]`` .................................... (2)


となっていて、これは、
「論理式 A を満たし、論理式 B を満たさない要素の数が 0 である」という意味です。
すなわち、
``| P |``、``&&``を論理和、``~~``を論理否定とすると、``|A && ~~ B| = 0``

Mathcomp では、xが集合の要素であること``x ∈ P`` と、
xが論理式Pを満たすこと ``P x``を同一視するのですが、
このことは、別の機会に説明します。


(1)と(2)は同値のはずですが、それを証明する補題がなかった（見つけられなかった）ので、
証明してみました。
*)

From mathcomp Require Import all_ssreflect.

Section Test.
  
  Variable T : finType.

(**
# 通常の論理式での証明
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
# boolean な論理式での証明
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
# おまけ (直接 boolean の式を証明する)
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

(* END *)
