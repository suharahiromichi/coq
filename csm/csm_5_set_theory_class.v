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
        axiom1 (A : M -> Prop) (x : M) : A x \/ ~(A x);
        axiom2 (A : M -> Prop) (x : M) : ~ ~ A x -> A x
    }.

  Check mySet : Type.
  Check MySet.                              (* 略 *)
  
  Section TEST1.
    Variable M : mySet.
    Variable x : M.
  End TEST1.
  
(*Definition belong {M : Type} (A : mySet M) (x : M) : Prop := A x. *)
  Definition belong {M : mySet} (A : M -> Prop) (x : M) : Prop := A x.
  Notation "x ∈ A" := (belong A x) (at level 11).

(*Definition myEmptySet {M : Type} : mySet M := fun (_ : M) => False. *)
(*Definition myMotherSet {M : Type} : mySet M := fun (_ : M) => True. *)
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

    Check @axiom1 M A x : A x \/ ~ A x.
    Check axiom1 A x : A x \/ ~ A x.
    Check @axiom2 M A x : ~ ~ A x -> A x.    
    
  End TEST2.
  
(*
  Lemma nnpp__dms : nnpp -> dms.
  Proof.
    move=> nnpp P Q Hn_nPnQ.
    apply: nnpp => Hn_PQ.
    apply: Hn_nPnQ.
    split=> H.
    - apply Hn_PQ.
        by left.
    - apply Hn_PQ.
        by right.
  Qed.
*)

(**
## 5.2 包含関係と統合
 *)
(*Definition mySub {M : Type} := fun (A B : mySet M) => forall (x : M), x ∈ A -> x ∈ B. *)
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
  Axiom axiom_ExteqmySet : forall {M : mySet} (A B : M -> Prop), eqmySet A B -> A = B.
  
(*Variable Mother : mySet. *)

  Lemma rfl_eqS {M : mySet} (A : M -> Prop) : A = A.
  Proof. by []. Qed.

  Lemma sym_eqS {M : mySet} (A B : M -> Prop) : A = B -> B = A.
  Proof.
    move=> HAB.
      by rewrite HAB.
  Qed.
  (* ここでは、まだ公理は使っていない。 *)

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
    - by move/(@axiom2 M A x).
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
    - case: (@axiom1 M A x) => H'.
      + by left.
      + by right.
  Qed.
  
End MySet.

(* END *)
