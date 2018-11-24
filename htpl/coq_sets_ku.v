Section SetTheory.
  
  (* 「Coqによる定理証明入門」 神戸大学 高橋先生 *)
  (* http://herb.h.kobe-u.ac.jp/coq/coq.pdf *)
  (* bullet を使ってリライトしています。演習問題の答えはありません。 *)
  
  Require Import Ensembles.
  Require Import Classical.
  
  Variable U : Type.
  Definition Shugo := Ensemble U.
  
  Notation "x ∈ A" := (In U A x) (at level 55,no associativity).
  Notation "A ⊆ B" := (Included U A B) (at level 54, no associativity).
  Notation "A ∩ B" := (Intersection U A B) (at level 53, right associativity).
  Notation "A ∪ B" := (Union U A B) (at level 53, right associativity).
  Notation "A \ B" := (Setminus U A B) (at level 52, no associativity).
  Notation ø := (Empty_set U).
  Notation Ω := (Full_set U).

  (* Variables A B C : Shugo. *)
  
  Lemma in_or_not (A : Shugo) : forall x, (x ∈ A) \/ ~ x ∈ A.
  Proof.
    intros x.
    now apply classic.
  Qed.
  
  Lemma bubun_traisitive A B C : A ⊆ B /\ B ⊆ C -> A ⊆ C.
  Proof.
    (* unfold Included. *)
    intros H x HxA.
    destruct H as [HAB HBC].
    apply HBC.
    now apply HAB.
  Qed.

  Lemma empty_bubun A : ø ⊆ A.
  Proof.
    (* unfold Included. *)
    intros x He.
    now destruct He.
  Qed.

  Lemma full_bubun A : A ⊆ Ω.
  Proof.
    (* unfold Included. *)
    intros x HxA.
    Check Full_intro : forall (U : Type) (x : U), In U (Full_set U) x.
    now apply Full_intro.
  Qed.
  
  Ltac seteq := apply Extensionality_Ensembles; unfold Same_set; split.
  
  Lemma union_id A : A ∪ A = A.
  Proof.
    seteq.
    - intros x HAA.
      now destruct HAA.
    - intros x HA.
      Check Union_introl.
      now apply Union_introl.
  Qed.

  Lemma union_comm A B : A ∪ B = B ∪ A.
  Proof.
    seteq.
    - intros x HxAB.
      destruct HxAB.
      + now apply Union_intror.
      + now apply Union_introl.
    - intros x HxBA.
      destruct HxBA.
      + now apply Union_intror.
      + now apply Union_introl.
  Qed.

  (*
  3. A∪(B∪C) = (A∪B)∪C
  4. A ⊆ A∪B, B ⊆ A∪B
  5. A, B ⊆ C → A∪B ⊆ C
   *)
  
  Lemma probA4b A B : A ∪ B = B -> A ⊆ B.
  Proof.
    intros HAB_B x HxA.
    rewrite <- HAB_B.
    now apply Union_introl.
  Qed.

  (*
  1. A∩A = A
  2. A∩B = B∩A
  3. A∩(B∩C) = (A∩B)∩C
  4. A∩B ⊆ A, A∩B ⊆ B
  5. C ⊆ A, B → C ⊆ A∩B
  6. A ⊆ B ⇔ A∩B = A
   *)
  
  (* 素集合 *)
  Lemma Kuu A B : Disjoint U A B <-> A ∩ B = ø.
  Proof.
    split.
    - intros Hd.
      seteq.
      + intros x HxAB.
        destruct Hd as [Hd].
        specialize (Hd x).
        easy.                               (* 前提が矛盾 *)
      + now apply empty_bubun.
    - intros HAB_E.
      apply Disjoint_intro.
      intros x.
      rewrite HAB_E.
      intros HxE.
      now destruct HxE.                     (* 前提にx∈ø で矛盾 *)
  Qed.

  Lemma probA7b A B C : A ∪ B = B ∩ C -> A ⊆ B /\ B ⊆ C.
  Proof.
    intros HAB_BC.
    split.
    - intros x HxA.
      assert (x ∈ A ∪ B).
      + now apply Union_introl; apply HxA.
      + rewrite HAB_BC in H.
        now destruct H.
    - intros x HxB.
      assert (x ∈ A ∪ B).
      + now apply Union_intror; apply HxB.
      + rewrite HAB_BC in H.
        now destruct H.
  Qed.
  
  (* \ の優先順位を変えている。 *)
  Lemma setminus A B : forall x, x ∈ A -> ~ x ∈ B -> x ∈ A \ B.
  Proof.
    intros x HxA HnxB.
    split.
    - easy.                                 (* x ∈ A *)
    - easy.                                 (* ~ x ∈ B *)
  Qed.
  
  Lemma probA8 A B : (A \ B) ∪ (A ∩ B) = A.
  Proof.
    seteq.
    - intros x H.
      destruct H as [x [HA HB] | x [HA HB]].
      + easy.
      + easy.
    - intros x.
      destruct (in_or_not B x).
      + intros HxA.
        apply Union_intror.
        now apply Intersection_intro.
      + intros HxA.
        apply Union_introl.
        now apply setminus.
  Qed.
  
  (* 集合族 *)

  Variable K : Type.
  Definition Fam := K -> Shugo.

  Inductive UnionF (X : Fam) : Shugo :=
    unionf_intro : forall x : U, (exists n : K, x ∈ X n) -> x ∈ UnionF X.
  
  Inductive InterF (X : Fam) : Shugo :=
    interf_intro : forall x : U, (forall n : K, x ∈ X n) -> x ∈ InterF X.
  
  Lemma mem_unionf F : forall n, F n ⊆ UnionF F.
  Proof.
    intros n x HxFn.
    apply unionf_intro.
    now exists n.
  Qed.
  
  Lemma mem_interf F : forall n, InterF F ⊆ F n.
  Proof.
    intros n x HIF.
    destruct HIF as [x HIF].
    specialize (HIF n).
    easy.
  Qed.
  
  Lemma unionf_inc F G : (forall n, F n ⊆ G n) -> UnionF F ⊆ UnionF G.
  Proof.
    intros HFG x H.
    destruct H as [x [n H]].
    apply unionf_intro.
    exists n.
    now apply (HFG n).
  Qed.
  
  Lemma interf_inc F G : (forall n, F n ⊆ G n) -> InterF F ⊆ InterF G.
  Proof.
    intros HFG x H.
    unfold Included in HFG.
    destruct H as [x H].
    apply interf_intro.
    intros n.
    specialize (HFG n x).
    specialize (H n).    
    now apply HFG.
  Qed.

End SetTheory.

(* END *)
