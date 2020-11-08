(**
Coq/SSReflect/MathComp による定理証明

5. 集合の形式化
======
2018_05_03 @suharahiromichi
2020_10_25 @morita_hm : 積集合関連の演算を追記
2020_11_09 @morita_hm : GitLab から Subset の像を追加
https://github.com/morita-hm/proofcafe_private/blob/main/csm_5_set_theory.v
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

Definition myEmptySet {M : Type} : mySet M := fun _ => False.
Definition myMotherSet {M : Type} : mySet M := fun _ => True.

(* 5.2 包含関係と統合 *)

Definition mySub {M : Type} := fun (A B : mySet M) => forall (x : M), x ∈ A -> x ∈ B.
Notation "A ⊂ B" := (mySub A B) (at level 11).

Section 包含関係.
  Variable M : Type.

  Check mySet M : Type.
  Check myEmptySet : mySet M.
  Check myMotherSet : mySet M.

  Lemma Sub_Mother (A : mySet M) : A ⊂ myMotherSet.
  Proof. by []. Qed.

  Lemma Sub_Empty (A : mySet M) : myEmptySet ⊂ A.
  Proof. by []. Qed.

  Lemma rfl_Sub (A : mySet M) : A ⊂ A.
  Proof. by []. Qed.

  Lemma transitive_Sub (A B C : mySet M) : A ⊂ B -> B ⊂ C -> A ⊂ C.
  Proof.
    move=> HAB HBC t HtA.
    apply: HBC.
    apply: HAB.
    apply: HtA.
  Qed.
End 包含関係.

Definition eqmySet {M : Type} := fun (A B : mySet M) => (A ⊂ B) /\ (B ⊂ A).
Axiom axiom_ExteqmySet : forall {M : Type} (A B : mySet M), eqmySet A B -> A = B.

Section 等号.
  Variable Mother : Type.

  Lemma rfl_eqS (A : mySet Mother) : A = A.
  Proof. by []. Qed.

  Lemma sym_eqS (A B : mySet Mother) : A = B -> B = A.
  Proof. move=> HAB. by rewrite HAB. Qed.

End 等号.

(* 5.3 集合上の演算 *)

Definition myComplement {M : Type} (A : mySet M) : mySet M := fun (x : M) => ~(A x).
Notation "A ^c" := (myComplement A) (at level 11).

Definition myCup {M : Type} (A B : mySet M) : mySet M := fun (x : M) => x ∈ A \/ x ∈ B.
Notation "A ∪ B" := (myCup A B) (at level 11).

Section 演算.
  Variable M : Type.

  Lemma cEmpty_Mother : (@myEmptySet M)^c = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
    by apply: conj; rewrite /myComplement => x HxM.
  Qed.
  
  Lemma cc_cancel (A : mySet M) : (A^c)^c = A.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    by apply: conj; rewrite /myComplement => x H;
       case: (axiom_mySet A x) => HxA.

    Restart.
    
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    rewrite /myComplement.
    apply: conj => x H.
    (* rewrite /mySub 代わりに => x している。 *)
    
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
        apply Hnot_xA.
        apply HxA.
      (* HxA : ~x∈A の 場合 *)
      + done.                               (* x∈A かつ ~x ∈ A  で矛盾 *)
  Qed.

  Lemma cMotehr_Empty : (@myMotherSet M)^c = myEmptySet.
  Proof.
      by rewrite -cEmpty_Mother cc_cancel.
  Qed.

  Lemma myCupA (A B C : mySet M) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    split => x [H | H].
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
    rewrite /eqmySet.
    split => [| x H].
    - done.
    - case: (axiom_mySet A x) => H';
        by [left | right].
  Qed.
End 演算.

(* 5.4 集合間の写像 *)

Definition myMap {M1 M2 : Type} (A : mySet M1) (B : mySet M2) (f : M1 -> M2) :=
  forall (x : M1), x ∈ A -> f x ∈ B.
Notation "f ∈Map A \to B" := (myMap A B f) (at level 11).

Definition MapCompo {M1 M2 M3 : Type} (f : M2 -> M3) (g : M1 -> M2) : M1 -> M3 :=
  fun (x : M1) => f (g x).
Notation "f ● g" := (MapCompo f g) (at level 11).

(* 像 *)
Definition ImgOf {M1 M2 : Type} (f : M1 -> M2) {A : mySet M1} {B : mySet M2}
           (_ : f ∈Map A \to B) : mySet M2 :=
  fun (y : M2) => exists (x : M1), y = f x /\ x ∈ A.

(* 部分集合の像 @morita_hm *)
Definition ImgOfSub {M1 M2 : Type} (f : M1 -> M2) {X : mySet M1} {Y : mySet M2}
           (_ : f ∈Map X \to Y) (A : mySet M1) : mySet M2 :=
  fun (y : M2) => exists (x : M1), y = f x /\ x ∈ A /\ A ⊂ X.

(* 部分集合の逆像 @morita_hm *)
Definition InvImgOfSub {M1 M2 : Type} (f : M1 -> M2) {X : mySet M1} {Y : mySet M2}
           (_ : f ∈Map X \to Y) (B : mySet M2) : mySet M1 :=
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
      + by apply gAB.
      + by apply gAB.
      + by apply H.
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

(* 5.5 fintype を用いた有限集合の形式化 *)

Definition p2S {M : finType} (pA : pred M) : mySet M :=
  fun (x : M) => if x \in pA then True else False.
Notation "\{ x 'in' pA \}" := (p2S pA).     (* x は飾り。 *)

Section fintypeを用いた有限集合.
  (* Set Printing Coercions. *)
  
  Variable M : finType.
  
  (* myMotherSet =
     p2S (pred_of_simpl (pred_of_argType (Equality.sort (Finite.eqType M)))) *)
  Check p2S M.
  Check p2S (mem M).
  Check p2S (pred_of_simpl (pred_of_argType (Equality.sort (Finite.eqType M)))).
  
  Lemma Mother_predT : myMotherSet = \{ x in M \}.
  Proof. by []. Qed.
  
  Lemma myFinBelongP (x : M) (pA : pred M) : reflect (x ∈ \{x in pA \}) (x \in pA).
  Proof.
    rewrite /belong /p2S.
    apply/(iffP idP) => H1.
    - Check (_ : (x \in pA) = true).
        by rewrite (_ : (x \in pA) = true).
    - have testH : (x \in pA) || ~~(x \in pA).
      + set t := x \in pA.
          by case: t.
      + move: testH.
        case/orP => [| Harg]; first by [].
        Check (_ : (x \in pA) = false).
        rewrite (_ : (x \in pA) = false) in H1; first by [].
        by apply: negbTE.
  Qed.
  
  (* suhara *)
  Lemma myFinBelongP' (x : M) (pA : pred M) : reflect (x ∈ \{x in pA \}) (x \in pA).
  Proof.
    rewrite /belong /p2S.
    apply/(iffP idP) => H1.
    - by rewrite H1.
    - by case H : (x \in pA); last rewrite H in H1.
  Qed.
  
  Lemma myFinSubsetP (pA pB : pred M) :
    reflect (\{ x in pA \} ⊂ \{ x in pB \}) (pA \subset pB).
  Proof.
    rewrite /mySub.
    apply/(iffP idP) => H.
    - move=> x /myFinBelongP => H2.
      apply/myFinBelongP.
      move: H => /subsetP.
      rewrite /sub_mem.
      by apply.
    - apply/subsetP.
      rewrite /sub_mem => x /myFinBelongP => HpA.
      apply/myFinBelongP.
      by apply H.
  Qed.
  
  (* fintype の補題 *)
  Check predT_subset : forall (T : finType) (A : pred T),
      T \subset A -> forall x : T, x \in A.
  
  Lemma Mother_Sub (pA : pred M) :
    myMotherSet ⊂ \{ x in pA \} -> forall x, x ∈ \{ x in pA \}.
  Proof.
    rewrite Mother_predT => /myFinSubsetP => H x.
    apply/myFinBelongP.
    by apply: predT_subset.
  Qed.

  (* fintype の補題 *)
  Check subset_trans : forall (T : finType) (A B C : pred T),
      A \subset B -> B \subset C -> A \subset C.

  Lemma transitive_Sub' (pA pB pC : pred M) :
    \{ x in pA \} ⊂ \{ x in pB \} ->
    \{ x in pB \} ⊂ \{ x in pC \} ->
    \{ x in pA \} ⊂ \{ x in pC \}.
  Proof.
    move/myFinSubsetP => HAB /myFinSubsetP HBC.
      by apply/myFinSubsetP/(subset_trans HAB HBC).
  Qed.

  Lemma transitive_Sub'' (pA pB pC : pred M) :
    \{ x in pA \} ⊂ \{ x in pB \} ->
    \{ x in pB \} ⊂ \{ x in pC \} ->
    \{ x in pA \} ⊂ \{ x in pC \}.
  Proof.
    by apply: transitive_Sub.
  Qed.
End fintypeを用いた有限集合.  

Section ライブラリfinsetの利用.
  Variable M : finType.

  Lemma demorgan (A B C : {set M}) : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
  Proof.
    apply/setP => x.
    rewrite !inE.                          (* || と && に変換する。 *)
    Check orb_andl.
    by rewrite -orb_andl.         (* || と && の ド・モルガンの定理 *)
  Qed.
End ライブラリfinsetの利用.

(* END *)
