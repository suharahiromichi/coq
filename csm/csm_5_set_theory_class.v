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
        A : pred M
    }.

  Check mySet : Type.
  Check MySet.                              (* 略 *)
  
  Section TEST1.
    Variable M : mySet.
    Variable x : M.
  End TEST1.
  
  Definition belong {M : mySet} (A : pred M) (x : M) : bool := A x.
  Notation "x ∈ A" := (belong A x) (at level 11).

  Definition myEmptySet {M : mySet} (_ : M) := false.
  Definition myMotherSet {M : mySet} (_ : M) := true.

  Section TEST2.
    Variable M : mySet.
    Variable A : pred M.
    Variable x : M.
    
    Check @myEmptySet : forall M : mySet, pred M.
    Check myEmptySet x.
    Check @belong M myEmptySet x.
    Check belong myEmptySet x.
    Check x ∈ myEmptySet.
  End TEST2.
  
(**
## 5.2 包含関係と統合
 *)
  Definition mySub {M : mySet} (A B : pred M) := forall (x : M), x ∈ A -> x ∈ B.
  Notation "A ⊂ B" := (mySub A B) (at level 11).

  Lemma Sub_Mother {M : mySet} (A : pred M) : A ⊂ myMotherSet.
  Proof. done. Qed.
  
  Lemma Sub_Empty {M : mySet} (A : pred M) : myEmptySet ⊂ A.
  Proof. done. Qed.
  
  Lemma rfl_Sub {M : mySet} (A : pred M) : A ⊂ A.
  Proof. done. Qed.

  Lemma transitive_Sub {M : mySet} (A B C : pred M) : A ⊂ B -> B ⊂ C -> A ⊂ C.
  Proof.
    move=> HAB HBC t HtA.
    apply: HBC.
    apply: HAB.
    apply: HtA.
  Qed.
  
(*
  集合の「=」は「=1」を使う。

  Definition eqmySet {M : mySet} (A B : pred M) := (A ⊂ B) /\ (B ⊂ A).
  Axiom axiom_ExteqmySet : forall {M : mySet} (A B : pred M), eqmySet A B -> A = B.
*)  
  Lemma rfl_eqS {M : mySet} (A : pred M) : A =1 A.
  Proof. by []. Qed.

  Lemma sym_eqS {M : mySet} (A B : pred M) : A =1 B -> B =1 A.
  Proof.
    move=> HAB.
      by apply: fsym.
  Qed.
  
(**
## 5.3 集合上の演算
 *)
  Definition myComplement {M : mySet} (A : pred M) := fun (x : M) => ~~ A x.
  Notation "A ^c" := (myComplement A) (at level 11).

  Definition myCup {M : mySet} (A B : pred M) := fun (x : M) => x ∈ A || x ∈ B.
  Notation "A ∪ B" := (myCup A B) (at level 11).

  (* 追加 *)
  Lemma complement_test {M : mySet} (A : pred M) :
    forall x, ~~ (x ∈ A) = x ∈ (A ^c).
  Proof. done. Qed.
  (* 追加終わり。 *)
  
  Lemma cEmpty_Mother {M : mySet} : (@myEmptySet M)^c =1 (@myMotherSet M).
  Proof.
(*  apply: axiom_ExteqmySet. *)
    move=> x.
    rewrite /myComplement /myEmptySet /myMotherSet /=.
    done.
  Qed.
  
  Lemma cc_cancel {M : mySet} (A : pred M) : (A^c)^c =1 A.
  Proof.
(*  apply: axiom_ExteqmySet.
    rewrite /eqmySet.
*)
    move=> x.
    rewrite /myComplement /=.
    rewrite Bool.negb_involutive.
    done.
  Qed.
  
  Lemma cMotehr_Empty {M : mySet} : (@myMotherSet M)^c =1 myEmptySet.
  Proof.
    move=> x.
      by rewrite /myComplement /myEmptySet /=.
  Qed.
  
  Lemma myCupA {M : mySet} (A B C : pred M) : (A ∪ B) ∪ C =1 A ∪ (B ∪ C).
  Proof.
(*  apply: axiom_ExteqmySet.
    rewrite /eqmySet. *)
    move=> x.
    apply/idP/idP.
    - case/orP.
      + case/orP => [H | H].
        * apply/orP.
            by left.
        * apply/orP.
          right.
          apply/orP.
            by left.
      + move=> H.
        apply/orP.
        right.
        apply/orP.
          by right.
    - case/orP.
      + move => H.
        apply/orP.
        left.
        apply/orP.
            by left.
      + case/orP => [H | H].
        * apply/orP.
          left.
          apply/orP.
            by right.
        * apply/orP.
          by right.
  Qed.
  
  Lemma myUnionCompMother {M : mySet} (A : pred M) (p : pred M) :
    A ∪ (A^c) =1 myMotherSet.
  Proof.
(*  apply: axiom_ExteqmySet. *)
    move=> x.
    rewrite /myCup /myComplement.
      by rewrite Bool.orb_negb_r.         (* 排中律 *)
  Qed.
End MySet.

Notation "x ∈ A" := (belong A x) (at level 11).
Notation "A ⊂ B" := (mySub A B) (at level 11).
Notation "A ^c" := (myComplement A) (at level 11).
Notation "A ∪ B" := (myCup A B) (at level 11).

Section Nat.

  Canonical nat_MySet (m : nat) := MySet (leq ^~ 5).

  Check nat_MySet 5 : mySet.

  Variable a : nat_MySet 5.
  Variable b : nat_MySet 5.
  Variable c : nat_MySet 5.

  Check 1 : nat_MySet 5.
  Check a : nat_MySet 5.
  Check b : nat_MySet 5.
  Check c : nat_MySet 5.

  Check (leq ^~ 0) : pred (nat_MySet 5).
  Check (leq ^~ 1) : pred (nat_MySet 5).
  Check (leq ^~ 2) : pred (nat_MySet 5).
  Check (leq ^~ 3) : pred (nat_MySet 5).
  Check (leq ^~ 4) : pred (nat_MySet 5).
  Check (leq ^~ 5) : pred (nat_MySet 5).
  Check (leq ^~ 6) : pred (nat_MySet 5).

  Check 1 ∈ (leq ^~ 3).
  Check a ∈ (leq ^~ 3).

  Goal (leq ^~ 5) =1 (leq ^~ 6).
  Proof.
  Admitted.
  
  Fail Goal ((leq ^~ 2) ∪ (leq ^~ 2)) =1 (leq ^~ 2).

End Nat.

Section FinType.

  Check @MySet finType.

  (* Canonical finType_MySet (m : nat) := MySet  *)
                                         
End FinType.

(* END *)
