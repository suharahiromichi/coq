(**
Coq/SSReflect/MathComp による定理証明

5. 集合の形式化
======
型クラスとしての実装例 - bool型を使う。
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

(* bool であるので、排中律の公理は導入しなくてよい。 *)  

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
    move=> x.
    rewrite /myComplement /myEmptySet /myMotherSet /=.
    done.
  Qed.
  
  Lemma cc_cancel {M : mySet} (A : pred M) : (A^c)^c =1 A.
  Proof.
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

  Check @MySet nat (leq ^~ 5).
  Canonical nat_MySet (m : nat) := MySet (leq ^~ m).

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

  Check (leq ^~ 2) ∪ (leq ^~ 2) : pred (nat_MySet 5).

  Goal (leq ^~ 5) =1 (leq ^~ 5).
  Proof.
      by move=> x.
  Qed.
  
  Goal ((leq ^~ 2) ∪ (leq ^~ 3)) =1 (leq ^~ 3) :> pred (nat_MySet 5).
  Proof.
    move=> x.
    rewrite /myCup /belong.
    apply/idP/idP => [/orP [H | H] | H].
    Check @leq_trans 2 x 3.
    - by apply: (@leq_trans 2 x 3).
    - done.
    - apply/orP.
        by right.
  Qed.
End Nat.

Section FinType.
(**
# 有限型

実は、以下において mem は、すべて省略可能である。
*)
  Section TEST5.
    Variable M : finType.

    Check M : finType.
    Check mem M : pred M.
    Check @MySet M (mem M).
    Check MySet (mem M).
  End TEST5.

  Canonical finMySet (M : finType) := MySet (mem M).
  
  Variable M : finType.
  Variable a : M.
  Variable p : pred M.

  Check pred (finMySet M).
  
  Check (mem M) : pred (finMySet M).
  Check (mem M) ∪ (mem M) : pred (finMySet M).
  Check a ∈ mem M.

  Goal a ∈ mem M.
  Proof.
    rewrite /belong.
    done.
  Qed.

(**
## myMotherSet の有限型版
*)
  Lemma Mother_predT : myMotherSet = mem M.
  Proof. done. Qed.
    
(**
## belong の有限型版
*)
  Lemma myFinBelongP (x : M) (pA : pred (finMySet M)) : reflect (x ∈ mem pA) (x \in pA).
  Proof.
    rewrite /belong.
      by apply/(iffP idP).
  Qed.
    
(**
## mySubset の有限型版
*)
  Lemma myFinSubsetP (pA pB : pred (finMySet M)) :
    reflect ((mem pA) ⊂ (mem pB)) (pA \subset pB).
  Proof.
    rewrite /mySub.
    apply/(iffP idP) => H.
    - move=> x H1.
      apply/myFinBelongP.
      move: H => /subsetP.
      rewrite /sub_mem.
      by apply.
    - apply/subsetP.
      rewrite /sub_mem => x /myFinBelongP => HpA.
      apply/myFinBelongP.
      by apply H.
  Qed.

  (* fintype.v の補題 ： 有限型としての部分集合 *)
  Check predT_subset : forall (T : finType) (A : pred T),
      T \subset A -> forall x : T, x \in A.
  
  (* predT_subset の mySet版 *)
  Lemma Mother_Sub (pA : pred (finMySet M)) :
    myMotherSet ⊂ mem pA -> forall x, x ∈ mem pA.
  Proof.
    move/myFinSubsetP.
    rewrite /myFinSubsetP => H x.
    apply: predT_subset.
    done.
  Qed.

  (* fintype.v の補題 *)
  Check subset_trans : forall (T : finType) (A B C : pred T),
      A \subset B -> B \subset C -> A \subset C.
  
  (* subset_trans の mySet版 *)
  Lemma transitive_Sub' (pA pB pC : pred (finMySet M)) :
    mem pA ⊂ mem pB ->
    mem pB ⊂ mem pC ->
    mem pA ⊂ mem pC.
  Proof.
    move/myFinSubsetP => HAB /myFinSubsetP HBC.
      by apply/myFinSubsetP/(subset_trans HAB HBC).
    Restart.
      by apply: transitive_Sub.               (* see. 5.2 *)
  Qed.

(**
# 有限型の実体としてのOridinal

先の M : finType の M を ordinal_finType n に置き換える。
*)
  Section Ordinal.
    
    (* 通常の ordinal の定義 *)
    Definition p0 := @Ordinal 5 0 is_true_true.
    Check p0 : 'I_5 : Type.
    Check p0 : ordinal_finType 5 : finType.
    Compute val p0.                           (* = 0 *)
    
    Definition p1 := @Ordinal 5 1 is_true_true.
    Definition p2 := @Ordinal 5 2 is_true_true.
    
(*
  (* MySetのインスタンスの定義 *)
    Definition ordinal_MySet (n : nat) := finMySet (ordinal_finType n).
    
    (* これは、以下によって新しい集合を定義することと同じである。 *)
    Check MySet (mem (ordinal_finType 5)).
    (* Canonical ordinal_MySet n := MySet (mem (ordinal_finType 5)) *)
    Goal forall n, MySet (mem (ordinal_finType n)) = ordinal_MySet n.
    Proof. done. Qed.
    
    Check ordinal_MySet 5.
    
    (* 以下における mem は省略可能である。 *)

    Check      eq_op p0  : pred 'I_5.       (* == *)
    Check mem (eq_op p0) : pred 'I_5.
    Check      eq_op p0  : pred (ordinal_MySet 5).
    Check mem (eq_op p0) : pred (ordinal_MySet 5).
    Check mem (eq_op p0) : pred (ordinal_MySet 5).
    Check mem (eq_op p1) : pred (ordinal_MySet 5).
    Check mem (eq_op p2) : pred (ordinal_MySet 5).
*)    
    
    Check      eq_op p0  : pred 'I_5.       (* == *)
    Check mem (eq_op p0) : pred 'I_5.
    Check      eq_op p0  : pred (ordinal_finType 5).
    Check mem (eq_op p0) : pred (ordinal_finType 5).
    
    (* finMySet の定義だけで、以下は使用可能である。
       mem も省略可能である。 *)
    
    Goal p0 ∈ ((mem (eq_op p0) ∪ mem (eq_op p1)) ∪ mem (eq_op p2)).
    Proof. done. Qed.
    Goal p1 ∈ ((mem (eq_op p0) ∪ mem (eq_op p1)) ∪ mem (eq_op p2)).
    Proof. done. Qed.
    Goal p2 ∈ ((mem (eq_op p0) ∪ mem (eq_op p1)) ∪ mem (eq_op p2)).
    Proof. done. Qed.
    
    Goal (mem (eq_op p0) ∪ mem (eq_op p1)) ∪ mem (eq_op p2)
       =1 mem (eq_op p0) ∪ (mem (eq_op p1) ∪ mem (eq_op p2)).
    Proof. by apply: myCupA. Qed.
    
(*
  memだけの例は解り難くするので、省いてもよい。
  
    Check mem 'I_5                : pred 'I_5.
    Check mem 'I_5                : pred (ordinal_MySet 5).
    Check mem (ordinal_finType 5) : pred (ordinal_MySet 5).

    Check p0 ∈ mem (ordinal_finType 5).
    Goal p0 ∈ mem (ordinal_finType 5).
    Proof. done. Qed.
 *)
  End Ordinal.
End FinType.

(**
# これは無理だろうか
*)
Section Seq.
  Canonical seq_MySet {T : eqType} (S : seq T) := MySet (mem S).

  Check seq_MySet [:: 1; 2; 3].
  Check mem [:: 1; 2; 3] : pred (seq_MySet [:: 1; 2; 3]).

  Check 1 ∈ mem [:: 1; 2; 3].
(* Goal 1 ∈ mem [:: 1; 2; 3] *)

End Seq.

(* END *)
