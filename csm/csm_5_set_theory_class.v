(**
Coq/SSReflect/MathComp による定理証明

5. 集合の形式化
======

bool述語をする例
*)

(**
# はじめに

テキストでは、mySet を Coqの述語 (Prop型) で定義しています。

```
Definition mySet (M : Type) := M -> Prop.
```


ここでは、bool述語で定義してみます。

```
Definition mySet (M : Type) := prod M.
```


これによって、ふたつのメリットがあります。

1. テキストで導入しているふたつの公理が不要になります。

- belong（∈）の決定性の公理

```
Axiom axiom_mySet : forall (M : Type) (A : mySet M), forall (x : M), x ∈ A \/ ~(x ∈ A).
```

belongがbool述語となるので、公理なしで決定性が保証されます。


- 集合の同値の定義のための公理

```
Definition eqmySet {M : Type} (A B : mySet M) := (A ⊂ B) /\ (B ⊂ A).

Axiom axiom_ExteqmySet : forall {M : Type} (A B : mySet M), eqmySet A B -> A = B.
```

この公理の代わりに、``=1`` で表される一階の等式を使います。

```
Definition eqfun (f g : B -> A) : Prop := forall x, f x = g x.
```

集合の定義がbool述語であるため、bool値が等しいことで、集合の同値が判断できます。


2. finType とのリフレクション

テキストでは、bool述語を Prop に変換する補助関数 p2S を導入していますが、
これが不要になります。

```
Definition p2S {M : finType} (pA : pred M) : mySet M :=
  fun (x : M) => if x \in pA then True else False.
Notation "\{ x 'in' pA \}" := (p2S pA).     (* x は飾り。 *)
```
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
  Definition mySet := pred.
  
  Definition belong {M : Type} (A : mySet M) (x : M) : bool := A x.
  Notation "x ∈ A" := (belong A x) (at level 11).

(**
bool であるので、排中律の公理は導入しなくてよい。
 *)  
  Definition myEmptySet {M : Type} : mySet M := fun (_ : M) => false.
  Definition myMotherSet {M : Type} : mySet M := fun (_ : M) => true.

(**
## 5.2 包含関係と統合
 *)
  Definition mySub {M : Type} (A B : mySet M) := forall (x : M), x ∈ A -> x ∈ B.
  Notation "A ⊂ B" := (mySub A B) (at level 11).

  Lemma Sub_Mother {M : Type} (A : mySet M) : A ⊂ myMotherSet.
  Proof. done. Qed.
  
  Lemma Sub_Empty {M : Type} (A : mySet M) : myEmptySet ⊂ A.
  Proof. done. Qed.
  
  Lemma rfl_Sub {M : Type} (A : mySet M) : A ⊂ A.
  Proof. done. Qed.

  Lemma transitive_Sub {M : Type} (A B C : mySet M) : A ⊂ B -> B ⊂ C -> A ⊂ C.
  Proof.
    move=> HAB HBC t HtA.
    apply: HBC.
    apply: HAB.
    apply: HtA.
  Qed.
  
(**
集合の「=」は「=1」を使う。
*)  
  Lemma rfl_eqS {M : Type} (A : mySet M) : A =1 A.
  Proof. by []. Qed.

  Lemma sym_eqS {M : Type} (A B : mySet M) : A =1 B -> B =1 A.
  Proof.
    move=> HAB.
      by apply: fsym.
  Qed.
  
(**
## 5.3 集合上の演算
 *)
  Definition myComplement {M : Type} (A : mySet M) := fun (x : M) => ~~ A x.
  Notation "A ^c" := (myComplement A) (at level 11).

  Definition myCup {M : Type} (A B : mySet M) := fun (x : M) => x ∈ A || x ∈ B.
  Notation "A ∪ B" := (myCup A B) (at level 11).

  (* 追加 *)
  Lemma complement_test {M : Type} (A : mySet M) :
    forall x, ~~ (x ∈ A) = x ∈ (A ^c).
  Proof. done. Qed.
  (* 追加終わり。 *)
  
  Lemma cEmpty_Mother {M : Type} : (@myEmptySet M)^c =1 (@myMotherSet M).
  Proof.
    move=> x.
    rewrite /myComplement /myEmptySet /myMotherSet /=.
    done.
  Qed.
  
  Lemma cc_cancel {M : Type} (A : mySet M) : (A^c)^c =1 A.
  Proof.
    move=> x.
    rewrite /myComplement /=.
    rewrite Bool.negb_involutive.
    done.
  Qed.
  
  Lemma cMotehr_Empty {M : Type} : (@myMotherSet M)^c =1 myEmptySet.
  Proof.
    move=> x.
      by rewrite /myComplement /myEmptySet /=.
  Qed.
  
  Lemma myCupA {M : Type} (A B C : mySet M) : (A ∪ B) ∪ C =1 A ∪ (B ∪ C).
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
  
  Lemma myUnionCompMother {M : Type} (A : mySet M) (p : mySet M) :
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

  Section NatTest.
    Variable x : nat.
    Variable p1 p2 : mySet nat.
    
    Check x ∈ p1 : bool.
    Check p1 ∪ p2 : mySet nat.
    Check p1 ⊂ p2 : Prop.
  End NatTest.
  
  Check eq_op 0 : mySet nat.
  Check eq_op 1 : mySet nat.
  Check eq_op 2 : mySet nat.
  Check eq_op 3 : mySet nat.
  Check eq_op 4 : mySet nat.
  Check eq_op 5 : mySet nat.
  Check eq_op 6 : mySet nat.
  Check leq ^~ 2 : mySet nat.

  Check 1 ∈ eq_op 5.
  Check 1 ∈ leq ^~ 2.

  Goal 1 ∈ (eq_op 5 ∪ leq ^~ 2).
  Proof. done. Qed.

  Goal eq_op 0 ∪ eq_op 1 ∪ eq_op 2 =1 leq ^~ 2.
  Proof.
      by case; [| case; [| case]].
  Qed.
End Nat.

Section FinType.
(**
# 有限型
*)
  Variable M : finType.

  Section FinMySetTest.
    Variable x : M.
    Variable p1 p2 : mySet M.
    
    Check x ∈ p1 : bool.
    Check p1 ∪ p2 : mySet M.
    Check p1 ⊂ p2 : Prop.
  End FinMySetTest.
  
(**
## myMotherSet の有限型版
*)
  Lemma Mother_predT : myMotherSet = M.
  Proof. done. Qed.
  
(**
## belong の有限型版
*)
  Lemma myFinBelongP (x : M) (pA : mySet M) : reflect (x ∈ pA) (x \in pA).
  Proof.
    rewrite /belong.
      by apply/(iffP idP).
  Qed.
  
(**
## mySubset の有限型版
*)
  Lemma myFinSubsetP (pA pB : mySet M) : reflect (pA ⊂ pB) (pA \subset pB).
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
  Check predT_subset : forall (M : finType) (A : mySet M),
      M \subset A -> forall x : M, x \in A.
  
  (* predT_subset の Type版 *)
  Lemma Mother_Sub (pA : mySet M) :
    myMotherSet ⊂ pA -> forall x, x ∈ pA.
  Proof.
    move/myFinSubsetP.
    rewrite /myFinSubsetP => H x.
    apply: predT_subset.
    done.
  Qed.
  
  (* fintype.v の補題 *)
  Check subset_trans : forall (T : finType) (A B C : predPredType T),
      A \subset B -> B \subset C -> A \subset C.
  
  (* subset_trans の Type版 *)
  Lemma transitive_Sub' (pA pB pC : mySet M) :
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
*)
  Section Ordinal.
    
(**
M : finType の M を ordinal_finType n に置き換える。
 *)
    Check M                 : finType.
    Check ordinal_finType 5 : finType.
    
    (* 通常の ordinal の定義 *)
    Definition p0 := @Ordinal 5 0 is_true_true.
    Check p0 : 'I_5 : Type.
    Check p0 : ordinal_finType 5 : finType.
    Compute val p0.                           (* = 0 *)
    
    Definition p1 := @Ordinal 5 1 is_true_true.
    Definition p2 := @Ordinal 5 2 is_true_true.
    
    Check      eq_op p0  : mySet 'I_5.       (* == *)
    Check      eq_op p0  : mySet (ordinal_finType 5).
    
    Goal p0 ∈ (eq_op p0 ∪ eq_op p1 ∪ eq_op p2).
    Proof. done. Qed.
    Goal p1 ∈ (eq_op p0 ∪ eq_op p1 ∪ eq_op p2).
    Proof. done. Qed.
    Goal p2 ∈ (eq_op p0 ∪ eq_op p1 ∪ eq_op p2).
    Proof. done. Qed.
    
    Goal (eq_op p0 ∪ eq_op p1) ∪ eq_op p2 =1 eq_op p0 ∪ (eq_op p1 ∪ eq_op p2).
    Proof. by apply: myCupA. Qed.
    
  End Ordinal.
End FinType.

(* END *)
