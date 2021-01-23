(**
Coq/SSReflect/MathComp による定理証明

5. 集合の形式化
======
2018_05_03 @suharahiromichi
2020_10_25 @morita_hm : 積集合関連の演算を追記
2020_11_09 @morita_hm : GitLab から Subset の像を追加
https://github.com/morita-hm/proofcafe_private/blob/main/csm_5_set_theory.v
 *)

(**
- csm_5_set_theory.v    全体の内容、および、演習問題 5.1の逆像
- csm_ex_5_1.v          演習問題 5.1 の積集合と差集合
- csm_ex_5_2_a.v        演習問題 5.2
- csm_ex_5_3_a.v        演習問題 5.3
- csm_ex_5_4.v          演習問題 5.4
- csm_ex_5_5.v          演習問題 5.5

- csm_5_set_theory_fintype.v   5.5 finsetを用いた有限集合の形式化（具体的な集合）
- csm_5_set_theory_finset.v    5.6 ライブラリfinset（5.5節までとは独立な内容)
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(* 5.1 集合、部分集合 *)
Definition mySet (M : Type) := M -> Prop.
Definition belong {M : Type} (A : mySet M) (x : M) : Prop := A x.
Notation "x ∈ A" := (belong A x) (at level 11).
Axiom axiom_mySet : forall (M : Type) (A : mySet M), forall (x : M), x ∈ A \/ ~(x ∈ A).

Definition myEmptySet {M : Type} : mySet M := fun (_ : M) => False.
Definition myMotherSet {M : Type} : mySet M := fun (_ : M) => True.

(* 5.2 包含関係と統合 *)

Definition mySub {M : Type} := fun (A B : mySet M) => forall (x : M), x ∈ A -> x ∈ B.
Notation "A ⊂ B" := (mySub A B) (at level 11).

Section 包含関係.
  Variable M : Type.

  Check mySet M : Type.
  Check myEmptySet : mySet M.
  Check myMotherSet : mySet M.

  Lemma Sub_Mother (A : mySet M) : A ⊂ myMotherSet.
  Proof.
    rewrite /mySub /myMotherSet /belong => x1 H.
    (* Goal : True *)
    done.

    Restart.
      by [].
  Qed.

  Lemma Sub_Empty (A : mySet M) : myEmptySet ⊂ A.
  Proof.
    rewrite /mySub /myEmptySet /belong => x1 H.
    (* H : False *)
    done.
    
    Restart.
      by [].
  Qed.

  Lemma rfl_Sub (A : mySet M) : A ⊂ A.
  Proof.
    rewrite /mySub /belong => x1 H.
      (* A x1 -> A x1 *)
    done.
    
    Restart.
      by [].
  Qed.

  Lemma transitive_Sub (A B C : mySet M) : A ⊂ B -> B ⊂ C -> A ⊂ C.
  Proof.
    move=> HAB HBC t HtA.
    (* HBC : B ⊂ C *)
    rewrite /mySub in HBC.  (* 省略可能である。 *)
    (* HBC : forall x : M, x ∈ B -> x ∈ C *)
    (* Goal : t ∈ C *)
    apply: HBC.
    (* Goal : t ∈ B *)
    
    apply: HAB.
    apply: HtA.

    Restart.
    move=> HAB HBC t HtA.
      by auto.                              (* 導出原理 *)
  Qed.
End 包含関係.

Definition eqmySet {M : Type} (A B : mySet M) := (A ⊂ B) /\ (B ⊂ A).
(* 公理を追加する。 *)
Axiom axiom_ExteqmySet : forall {M : Type} (A B : mySet M), eqmySet A B -> A = B.

Section 等号.
  Variable Mother : Type.

  Lemma rfl_eqS (A : mySet Mother) : A = A.
  Proof. by []. Qed.

  Lemma sym_eqS (A B : mySet Mother) : A = B -> B = A.
  Proof.
    move=> HAB.
      by rewrite HAB.
  Qed.
  
  (* ここでは、まだ公理は使っていない。 *)
End 等号.

(* 5.3 集合上の演算 *)

Definition myComplement {M : Type} (A : mySet M) : mySet M := fun (x : M) => ~(A x).
Notation "A ^c" := (myComplement A) (at level 11).

Definition myCup {M : Type} (A B : mySet M) : mySet M := fun (x : M) => x ∈ A \/ x ∈ B.
Notation "A ∪ B" := (myCup A B) (at level 11).

Section 演算.
  Variable M : Type.

  (* 追加 *)
  Lemma complement_test x (A : mySet M) : ~ (x ∈ A) <-> x ∈ (A ^c).
  Proof.
    rewrite /myComplement /belong.
    done.
  Qed.
  (* 追加終わり。 *)
  Lemma cEmpty_Mother : (@myEmptySet M)^c = (@myMotherSet M).
  Proof.
    apply: axiom_ExteqmySet.                (* 公理を使用する。 *)
    rewrite /eqmySet.                       (* 省略可能 *)
    split=> x HxM.
    (* Goal : x ∈ myMotherSet *)
    - rewrite /belong.
      done.

    (* Goal : ~ (x ∈ myEmptySet) *)
    - rewrite /myComplement.
      apply/complement_test.                (* 省略可能 *)
      done.
      
    Restart.
    apply: axiom_ExteqmySet.                (* 公理を使用する。 *)
      by apply: conj; rewrite /myComplement => x HxM.
  Qed.
  
  Lemma cc_cancel (A : mySet M) : (A^c)^c = A.
  Proof.
    apply: axiom_ExteqmySet.                (* 公理を使用する。 *)
    rewrite /eqmySet.
    by apply: conj; rewrite /myComplement => x H;
       case: (axiom_mySet A x) => HxA.

    Restart.
    
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    rewrite /myComplement.
    rewrite /mySub.
    split=> x H.
    
    Check (axiom_mySet A x) : x ∈ A \/ ~(x ∈ A).
    
    - case: (axiom_mySet A x) => HxA.
      (* HxA : x∈A の 場合 *)
      + done.
      (* HxA : ~x∈A の 場合 *)
      + Check H HxA : False.
        move/H in HxA.                      (* HxA : False で矛盾 *)
        done.
        
    - case: (axiom_mySet A x) => HxA.
      (* HxA : x∈A の 場合 *)
      + move=> Hnot_xA.                     (* 二重否定を除去する。 *)
        apply: Hnot_xA.
          by apply: HxA.
      (* HxA : ~x∈A の 場合 *)
      + done.                               (* x∈A かつ ~x ∈ A  で矛盾 *)
  Qed.
  
  Lemma cMotehr_Empty : (@myMotherSet M)^c = myEmptySet.
  Proof.
      by rewrite -cEmpty_Mother cc_cancel.
      
      Restart.
    rewrite -cEmpty_Mother.
    rewrite cc_cancel.
    done.
  Qed.
  
  Lemma myCupA (A B C : mySet M) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
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
  
  Lemma myUnionCompMother (A : mySet M) : A ∪ (A^c) = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
(*  rewrite /eqmySet /myComplement /myMotherSet /myCup. *)
    split => [x | x H].
    (* (A ∪ (A ^c)) ⊂ myMotherSet *)
    - done.
      
    (* (A ∪ (A ^c)) ⊃ myMothearSet*)
    - case: (axiom_mySet A x) => H'.        (* ; by [left | right] *)
      (* H' : x ∈ A  *)
      + left.
      (* Goal : x ∈ A *)
        done.
        
      (* H' : ~ (x ∈ A) *)
      + right.
        (* Goal : x ∈ (A ^c) *)
        done.
  Qed.
End 演算.

(* 5.4 集合間の写像 *)

Definition myMap {M1 M2 : Type} (A : mySet M1) (B : mySet M2) (f : M1 -> M2) :=
  forall (x : M1), x ∈ A -> f x ∈ B.
Notation "f ∈Map A \to B" := (myMap A B f) (at level 11).

Definition MapCompo {M1 M2 M3 : Type} (f : M2 -> M3) (g : M1 -> M2) : M1 -> M3 :=
  fun (x : M1) => f (g x).
Notation "f ● g" := (MapCompo f g) (at level 11).

(* 定義域Xの像Y *)
(* これだと、部分集合の像を扱うのが難しいので、問5.2を解くためには使わない。 *)
Definition ImgOf {M1 M2 : Type} (f : M1 -> M2) {X : mySet M1} {Y : mySet M2}
           (_ : f ∈Map X \to Y) : mySet M2 :=
  fun (y : M2) => exists (x : M1), y = f x /\ x ∈ X.

(* 定義域Xの部分集合Aの像B @morita_hm - Bについては全射であること。 *)
(* 問5.2のために、部分集合の像を定義するために、定義した。 *)
Definition ImgOfSub {M1 M2 : Type} (f : M1 -> M2) {X : mySet M1} {Y : mySet M2}
           (_ : f ∈Map X \to Y) (A : mySet M1) : mySet M2 :=
  (*                             ~~~~~~~~~~~~~~   ~~~~~~~ *)
  fun (y : M2) => exists (x : M1), y = f x /\ x ∈ A /\ A ⊂ X.

(* 値域Yの部分集合Bの逆像A @morita_hm - Bについては全射であること。 *)
(* 問5.3のために、部分集合の逆像を定義するために、定義した。 *)
Definition InvImgOfSub {M1 M2 : Type} (f : M1 -> M2) {X : mySet M1} {Y : mySet M2}
           (_ : f ∈Map X \to Y) (B : mySet M2) : mySet M1 :=
  (*                             ~~~~~~~~~~~~~~   ~~~~~~~ *)
  fun (x : M1) => exists (y : M2), y = f x /\ y ∈ B /\ B ⊂ Y.

(* 単射 *)
Definition mySetInj {M1 M2 : Type} (f : M1 -> M2) {A : mySet M1} {B : mySet M2}
           (_ : f ∈Map A \to B) : Prop :=
  forall (x y : M1), x ∈ A -> y ∈ A -> f x = f y -> x = y.

(* 全射 *)
Definition mySetSur {M1 M2 : Type} (f : M1 -> M2) {A : mySet M1} {B : mySet M2}
           (_ : f ∈Map A \to B) : Prop :=
  forall (y : M2), y ∈ B -> exists (x : M1), x ∈ A -> f x = y.

(* 全単射 *)
Definition mySetBi {M1 M2 : Type} (f : M1 -> M2) {A : mySet M1} {B : mySet M2}
           (fAB : f ∈Map A \to B) : Prop :=
  mySetInj fAB /\ mySetSur fAB.


Section 写像.
  Variable M1 M2 M3 : Type.
  Variable f : M2 -> M3.
  Variable g : M1 -> M2.
  Variable A : mySet M1.
  Variable B : mySet M2.
  Variable C : mySet M3.
  Hypothesis gAB : g ∈Map A \to B.
  Hypothesis fBC : f ∈Map B \to C.
  
  Lemma transitive_Inj (fgAC : (f ● g) ∈Map A \to C) :
    mySetInj fBC -> mySetInj gAB -> mySetInj fgAC.
  Proof.
    rewrite /mySetInj => Hinjf Hinjg x y HxA HyA H.
    Check Hinjg x y HxA HyA.
    Check Hinjf (g x) (g y) (gAB HxA) (gAB HyA).
    apply: Hinjg.
    - done.
    - done.
      apply: Hinjf.
      + by apply: gAB.
      + by apply: gAB.
      + by apply: H.
  Qed.
  
  Lemma CompoTrans : (f ● g) ∈Map A \to C.
  Proof.
    move: gAB fBC.
    rewrite /MapCompo /myMap => Hab Hbc t Ha.
    apply: Hbc.
    apply: Hab.
    apply: Ha.
  Qed.
  
  Lemma ImSub : (ImgOf gAB) ⊂ B.
  Proof.
    rewrite /ImgOf => t.
    case=> x.
    case=> H1 H2.
    rewrite H1.
      by apply: gAB.
  Qed.
End 写像.
  
(* END *)
