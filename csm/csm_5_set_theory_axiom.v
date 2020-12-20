(**
「Coq/SSReflect/MathCompによる定理証明」第5章で導入された公理について
========================

@suharahiromichi

2020/12/26
 *)

(**
# はじめに

文献 [1.] （以下、テキストと呼びます）の第5章では集合形式化について説明されています。
そこでは、ふたつの公理が導入されています。

5章の冒頭に記載されているとおり、形式化の方法は一通りではないため、
別な公理や公理を導入しないで済ますことができないか、考えてたいと思います。
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
# 集合の形式化（復習）

型 M の要素である元 x が、型Mの要素全体を母集合とする集合 A に属することを、
M型を引数とする命題型P （すなわち M -> Prop) の型をもつ命題によってあらわす
（テキストのことばでいうと「形式化」することにします。

なお、型Mは任意な型とします。あとで制限することになるので、注意しておいてください。
*)

Definition mySet (M : Type) := M -> Prop.
Definition belong {M : Type} (A : mySet M) (x : M) : Prop := A x.
Notation "x ∈ A" := (belong A x) (at level 11).

Definition myEmptySet {M : Type} : mySet M := fun (_ : M) => False.
Definition myMotherSet {M : Type} : mySet M := fun (_ : M) => True.

Definition mySub {M : Type} := fun (A B : mySet M) => forall (x : M), x ∈ A -> x ∈ B.
Notation "A ⊂ B" := (mySub A B) (at level 11).
Definition eqmySet {M : Type} (A B : mySet M) := (A ⊂ B) /\ (B ⊂ A).

Definition myComplement {M : Type} (A : mySet M) : mySet M := fun (x : M) => ~(A x).
Notation "A ^c" := (myComplement A) (at level 11).

Definition myCup {M : Type} (A B : mySet M) : mySet M := fun (x : M) => x ∈ A \/ x ∈ B.
Notation "A ∪ B" := (myCup A B) (at level 11).

(**
# CSMの第5章の公理

上記の集合の形式化の定義には問題がふたつあります。（要補足）

- 元xが集合Aに含まれることは言えても、含まれないと言えるとは限らない。

これは、Coqが採用する直観主義論理の立場から、命題が証明できればそれが真だといえます。
しかし、命題が証明できないと言い切ることができない（場合がある）ため、
偽であるとの証明ができない（できるとは限らない）からです。

- 集合AがBに含まれ、かつ、BがAに含まれることから、集合AとBが等しいことを証明できない。

これは、Coqの等号``=``は、ライプニッツの等式といって、
その型の(Inductiveな)定義に遡って「同じに見える」場合に限り成立します。

例 ``1 + 1 = 2`` は、``S (S O) = S (S O)``

この場合、集合AとBが等しいこと ``(A ⊂ B) /\ (B ⊂ A)``
は集合の帰納的な定義に基づくものでないため ``A = B`` というこができません。

結果として、テキストの本文にあるように、
「補集合の補集合がもとの集合になること」の証明ができません。
テキストではふたつの公理を導入することで解決しています。
ここでは、それぞれを「公理 1」「公理 2」と呼ぶことにします。
*)

(**
## (公理 1.) axiom_mySet

テキストの第5章に沿って、
「元xが集合Aに含まれるか、含まれないかのどちらかである」を公理として導入します。
 *)

Axiom axiom_mySet : forall (M : Type) (A : mySet M), forall (x : M), x ∈ A \/ ~(x ∈ A).

(**
## (公理 2.) axiom_ExteqmySet

テキストの第5章に沿って、集合AとBが等しいことを、
集合AがBに含まれ、かつ、BがAに含まれることとして定義します。
 *)

Axiom axiom_ExteqmySet : forall {M : Type} (A B : mySet M), eqmySet A B -> A = B.

(**
## 補集合の補集合の証明
*)
Section Test1.
  Variable M : Type.                        (* 注意してください。 *)

  Lemma cc_cancel (A : mySet M) : (A^c)^c = A.
  Proof.
    apply: axiom_ExteqmySet.
    split; rewrite /myComplement => x H;
      by case: (axiom_mySet A x) => HxA.
  Qed.
  
  Lemma myUnionCompMother (A : mySet M) : A ∪ (A^c) = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
    split=> [x | x H] //=.
    case: (axiom_mySet A x); by [left | right].
  Qed.
End Test1.

(**
# 公理 1.について

## morita_hmさんの公理 ``refl_mySet``

ProofCafe において @morita_hm さんから別の公理が提案されました。より単純な、

``reflect (A x) true``

から、公理 1.を導くものです。
*)

Section Morita.
  Variable M : Type.                        (* 注意してください。 *)
  
  Axiom refl_mySet : forall (A : mySet M) (x : M), reflect (A x) true.
  
  Lemma axiom_mySet' : forall (A : mySet M),
      forall (x : M), x ∈ A \/ ~(x ∈ A).
  Proof.
    rewrite /belong => A x.
      by case: (refl_mySet A x); [left | right].
    Undo.
    move: (@refl_mySet A x) => Hr. (* ここで refl_mySet に M A x を与えている。 *)
    case: Hr.
    - by left.
    - by right.
  Qed.
  
(**
ここで実際に証明しているのは、次の命題であることが解ります。
*)
  Goal forall (A : mySet M) (x : M),
      reflect (A x) true -> x ∈ A \/ ~(x ∈ A).
  Proof.
    move=> A x.
    by case; [left | right].
  Qed.
End Morita.

(**
## 別の説明

公理 ``refl_mySet`` は、かたちを変えた排中律であり、
排中律を経由して公理 1.を証明していることになります。これを以下で説明します。
*)

(**
文献[2.] p.101 にあるとおり、``reflect P b`` は、

- 命題(Prop型の) P がTrueであると証明できるとき、 bool型の命題が真(true)である。

- 命題(Prop型の) P がFalseであると証明できるとき、bool型の命題が偽(false)である。

と場合分けできることを示します。
*)
Section Test2.
  
  Lemma A_ref (P : Prop) : P -> reflect P true.
  Proof.
    move=> H.
      by apply: ReflectT.
  Qed.
  
  Lemma notA_ref (P : Prop) : ~ P -> reflect P false.
  Proof.
    move=> H.
      by apply: ReflectF.
  Qed.

(**
場合分けができ、また、bool型の命題 true が false であるとは、false のことですから、
``reflect P true`` から排中律を導くことができます。
*)
  Lemma refl_exmid (P : Prop): reflect P true -> P \/ ~ P.
  Proof.
    case=> Hr.
    - by left.
    - by right.
  Qed.
End Test2.

(**
## 依存和の使用

かたちを変えた排中律としては、依存和があります。
命題 P が P または ~ P のどちらかに決定可能である、
ということから排中律が求められます。
*) 

Section Depend.
  Lemma dec_exmid (P : Prop) : {P} + {~ P} -> P \/ ~ P.
  Proof.
    case=> Hd.
    - by left.
    - by right.
  Qed.

End Depend.

(**
## finType の場合

テキストの 5.5節にあるように、
母集合にあたる型 M を任意の型から、有限型 (finType) に制限することでも、
公理 1.を不要にすることもできます。
 *)

Section FinType.
  Variable M : finType.             (* これまでは ``M : Type`` だった。 *)
  
(**
なぜなら、有限型（母集合が有限）ならば、元が集合に含まれるかどうかを決定する命題を
定義することができるからです。

このような命題はbool型の値をとるようにすると扱いやすいので、pA であらわします。
そして、bool述語 pA が x で成り立つときことを
MathCompの演算子 \in を使って ``x \in pA`` とあらわします。

- pA は ``pred M`` 型となっていますが、これは ``M -> bool`` のことです（深い意味は無い）。

- ``x \in pA`` を ``pA x`` に置き換えても（ここでは）同じです。
ただし、単純な構文糖衣ではないので、つねに同じであるわけではありません。
以下の説明も参照してください。

https://github.com/suharahiromichi/coq/blob/master/csm/csm_4_1_ssrbool.v
*)

(**
``pA : pred M`` が ``P : mySet M`` で形式化された集合の定で使えるように、
変換する関数 p2S を定義します。
なお、テキストで定義されている構文糖衣 ``\{ x 'in' pA \}`` は使わないことにしました。
すなわち `` \{ x in M \}`` は ``p2S M`` のことで x に意味はありません。
*)  
  Definition p2S (pA : pred M) : mySet M :=
    fun (x : M) => if x \in pA then True else False.

  Lemma Mother_predT : myMotherSet = p2S M.
  Proof. by []. Qed.

  Lemma myFinBelongP (x : M) (pA : pred M) : reflect (x ∈ p2S pA) (x \in pA).
  Proof.
    rewrite /belong /p2S.
    apply/(iffP idP) => H1.
    - by rewrite H1.
    - by case H : (x \in pA); last rewrite H in H1.
  Qed.  

(**
「元xが集合Aに含まれるか、含まれないかのどちらかである」ことを(公理 1.)を使わずに、
定理として導くことができます。
*)

  Lemma fin_mySet (pA : pred M) (x : M) : x \in pA \/ ~(x \in pA).
  Proof.
    case: (myFinBelongP x pA); by [left | right].
  Qed.

(**
実際の集合の証明では、``M : Type, P : mySet M``
を ``M : finType, pA : pred M`` に変更する必要があります。
*)
  Lemma Mother_Sub (pA : pred M) :
    myMotherSet ⊂ p2S pA -> forall x, x ∈ p2S pA.
  Proof.
    rewrite Mother_predT.
    move=> H x.
    Check H x : x ∈ p2S M -> x ∈ p2S pA.
    apply: (H x).
    done.
  Qed.
  
  Lemma transitive_Sub (pA pB pC : pred M) :
    pA ⊂ pB -> pB ⊂ pC -> pA ⊂ pC.
  Proof.
    move=> HAB HBC t HtA.
      by auto.
  Qed.

(**
axiom_mySet ではなく、fin_mySet を使って証明することができます。
すなわち(公理 1.)を使用せずに証明できたことになります。
*)  
  Lemma cc_cancel' (pA : pred M) : (pA^c)^c = pA.
  Proof.
    apply: axiom_ExteqmySet.
    split; rewrite /myComplement => x H;
      by case: (fin_mySet pA x) => HxA.
  Qed.

  Lemma myUnionCompMother' (pA : pred M) : pA ∪ (pA^c) = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
    split=> [x | x H] //=.
    case: (fin_mySet pA x); by [left | right].
  Qed.
End FinType.

Section 具体的なfinType.
  
  Definition p0 := @Ordinal 5 0 is_true_true.
  Check p2S 'I_5 : mySet 'I_5.  

  Goal p0 ∈ p2S 'I_5.
  Proof. by []. Qed.

End 具体的なfinType.

(**
## mySet を bool型であらわす場合

そもそも ``mySet M`` を bool型の ``pred M`` であらわすことで、公理 1.は不要になります。
belongがbool述語となるので、公理なしで決定性が保証されるからです。以下を参照してください。

https://github.com/suharahiromichi/coq/blob/master/csm/csm_5_set_theory_class.v

（ご注意。ファイル名に意味はありません）
 *)

(**
# 公理 2. について

これは、外延性の公理です。
*)

Section Test3.
  Variable M : finType.                     (* 注意してください。 *)

  Definition myMotherSet' : mySet M := fun (_ : M) => true.
  
  Lemma cc_cancel'' (pA : pred M) : (pA^c)^c =1 pA.
  Proof.
    move=> x.
    rewrite /myComplement.
    (* Goal : (~ ~ pA x) = pA x *)
  Admitted.

  Lemma myUnionCompMother'' (pA : pred M) : (pA ∪ (pA^c)) =1 myMotherSet'.
  Proof.
    move=> x.
    case: (fin_mySet pA x).
    move/myFinBelongP=> H.
    rewrite /myCup /myComplement /myMotherSet'.
  Admitted.
  
End Test3.

(**
# 文献

[1.] 萩原学 アフェルト・レナルド、「Coq/SSReflect/MathCompによる定理証明」、森北出版

[2.] Mathematical Components (MathComp Book) https://math-comp.github.io
 *)

(* END *)
