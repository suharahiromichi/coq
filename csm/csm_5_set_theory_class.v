(**
Coq/SSReflect/MathComp による定理証明

5. 集合の形式化
======
型クラスとしての実装例
*)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Section MySet.
(**
## 5.1 集合、部分集合
 *)
  Record mySet : Type :=                    (* 型クラス *)
    MySet {
        M :> Type;
        A : M -> Prop;
        axiom (A : M -> Prop) (x : M) : reflect (A x) true
(*      nnpp (A : M -> Prop) (x : M) : ~ ~ A x -> A x *)
    }.

  Check mySet : Type.
  Check MySet.                              (* 略 *)
  
  Section TEST1.
    Variable M : mySet.
    Variable x : M.
  End TEST1.
  
  Definition belong {M : mySet} (A : M -> Prop) (x : M) : Prop := A x.
  Notation "x ∈ A" := (belong A x) (at level 11).

  Definition myEmptySet {M : mySet} (_ : M) := False.
  Definition myMotherSet {M : mySet} (_ : M) := True.

  Section TEST2.
    Variable M : mySet.
    Variable A : M -> Prop.
    Variable x : M.
    
    Check @myEmptySet : forall M : mySet, M -> Prop.
    Check myEmptySet x.
    Check @belong M myEmptySet x.
    Check belong myEmptySet x.
    Check x ∈ myEmptySet.
  End TEST2.
  
  (* classically の成り立つ条件を一般化する。 *)
  (* 命題 P をリフレクトできる ブール式 b があれば、classically P は成り立つ。 *)
  Lemma classic_p (P : Prop) (b : bool) : reflect P b -> classically P -> P.
  Proof.
    move=> Hr Hc.
    apply/Hr.
    apply: Hc.
    move/Hr.
    done.
  Qed.
  
(* 命題 P をリフレクトできる ブール式 b があれば、二重否定除去は成り立つ。 *)
  Lemma nnpp_p (P : Prop) (b : bool) : reflect P b -> ~ ~ P -> P.
  Proof.
    move=> Hr Hnn.
    apply: classic_p.
    - by apply: Hr.
    - by apply/classicP.
  Qed.

(* 命題 P をリフレクトできる ブール式 b があれば、排中律は成り立つ。 *)
  Lemma exmid_p (P : Prop) (b : bool) : reflect P b -> P \/ ~ P.
  Proof.
    move=> Href.
    move: (Href).                           (* 見直すこと。 *)
    case/(iffP idP) => H.
    - move/introT in Href.
        by apply: Href.
    - by left.
    - by right.
  Qed.
  
  Section TEST3.
    Variable M : mySet.
    Variable A : M -> Prop.
    Variable x : M.

    Check @axiom M A x : reflect (A x) true.
    Check axiom A x : reflect (A x) true.
    Check @nnpp_p (A x) true (axiom A x) : ~ ~ A x -> A x.
    
    Check nnpp_p (axiom A x) : ~ ~ A x -> A x.
    Check exmid_p (axiom A x) : A x \/ ~ A x.
  End TEST3.

  Lemma nnpp {M : mySet} (A : M -> Prop) (x : M) : ~ ~ A x -> A x.
  Proof.
    apply: nnpp_p.
      by apply: axiom.
  Qed.

  Lemma exmid {M : mySet} (A : M -> Prop) (x : M) : A x \/ ~ A x.
  Proof.
    apply: exmid_p.
      by apply: axiom.
  Qed.
  
(**
## 5.2 包含関係と統合
 *)
  Definition mySub {M : mySet} (A B : M -> Prop) := forall (x : M), x ∈ A -> x ∈ B.
  Notation "A ⊂ B" := (mySub A B) (at level 11).

  Lemma Sub_Mother {M : mySet} (A : M -> Prop) : A ⊂ myMotherSet.
  Proof. by []. Qed.
  
  Lemma Sub_Empty {M : mySet} (A : M -> Prop) : myEmptySet ⊂ A.
  Proof. by []. Qed.

  Lemma rfl_Sub {M : mySet} (A : M -> Prop) : A ⊂ A.
  Proof. by []. Qed.

  Lemma transitive_Sub {M : mySet} (A B C : M -> Prop) : A ⊂ B -> B ⊂ C -> A ⊂ C.
  Proof.
    move=> HAB HBC t HtA.
    apply: HBC.
    apply: HAB.
    apply: HtA.
  Qed.

  Definition eqmySet {M : mySet} (A B : M -> Prop) := (A ⊂ B) /\ (B ⊂ A).
  (* まだ公理が残っている。 *)
  Axiom axiom_ExteqmySet : forall {M : mySet} (A B : M -> Prop), eqmySet A B -> A = B.
  
  Lemma rfl_eqS {M : mySet} (A : M -> Prop) : A = A.
  Proof. by []. Qed.

  Lemma sym_eqS {M : mySet} (A B : M -> Prop) : A = B -> B = A.
  Proof.
    move=> HAB.
      by rewrite HAB.
  Qed.
  
(**
## 5.3 集合上の演算
 *)
  Definition myComplement {M : mySet} (A : M -> Prop) := fun (x : M) => ~(A x).
  Notation "A ^c" := (myComplement A) (at level 11).

  Definition myCup {M : mySet} (A B : M -> Prop) := fun (x : M) => x ∈ A \/ x ∈ B.
  Notation "A ∪ B" := (myCup A B) (at level 11).

  (* 追加 *)
  Lemma complement_test {M : mySet} (A : M -> Prop) :
    forall x, ~ (x ∈ A) <-> x ∈ (A ^c).
  Proof. done. Qed.
  (* 追加終わり。 *)
  
  Lemma cEmpty_Mother {M : mySet} : (@myEmptySet M)^c = (@myMotherSet M).
  Proof.
    apply: axiom_ExteqmySet.
      by apply: conj; rewrite /myComplement => x HxM.
  Qed.
  
  Lemma cc_cancel {M : mySet} (A : M -> Prop) : (A^c)^c = A.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    apply: conj; rewrite /myComplement => x.
    - by move/(@nnpp M A x).
    - by move=> H.
  Qed.
  
  Lemma cMotehr_Empty {M : mySet} : (@myMotherSet M)^c = myEmptySet.
  Proof.
      by rewrite -cEmpty_Mother cc_cancel.
  Qed.
  
  Lemma myCupA {M : mySet} (A B C : M -> Prop) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    split=> x [H | H].
    - case: H => H.
      + by left.
      + by right; left.
    - by right; right.
    - by left; left.
    - case: H => H.
      + by left; right.
      + by right.
  Qed.
  
  Lemma myUnionCompMother {M : mySet} (A : M -> Prop) : A ∪ (A^c) = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
    split => [x | x H].
    - done.
    - case: (@exmid M A x) => H'.
      + by left.
      + by right.
  Qed.

End MySet.

(* END *)
