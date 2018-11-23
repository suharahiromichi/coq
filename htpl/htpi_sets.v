Section Sets.
  
  (* 「Coqによる定理証明入門」 神戸大学 高橋先生 *)
  (* http://herb.h.kobe-u.ac.jp/coq/coq.pdf *)
  
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

  (* HTPI *)
  
  (*
    Example 3.2.1. Suppose A ∩ C ⊆ B and a ∈ C. Prove that ~ a ∈ A \ B.
   *)

  Lemma ex3_2_1 A B C : forall a, A ∩ C ⊆ B /\ a ∈ C -> ~ a ∈ A \ B.
  Proof.
    intros a [HAC HaC] HaAB.
    destruct HaAB as [HaA HnaB].
    apply HnaB; clear HnaB.
    (*
      Givens 
      A ∩ C ⊆B
      a ∈ C
      a ∈ A
      
      Goal
      a ∈ B
     *)
    specialize (HAC a).                     (* !!!! *)
    apply HAC.
    now split.
  Qed.
  
  (*
    Example 3.2.3. Suppose A, B, and C are sets, A \ B ⊆ C, and x is anything at all.
    Prove that if x ∈ A \ C then x ∈ B.
   *)
  
  Lemma ex3_2_3 A B C : A \ B ⊆ C -> forall x, x ∈ A \ C -> x ∈ B.
  Proof.
    intros HABC x HxAC.
    destruct HxAC as [HxA HnxC].
    apply NNPP.
    intros HnxB.
    apply HnxC.
    (*
      Givens
      A \ B ⊆C
      x ∈ A
      ~ x ∈ C
      ~ x ∈ B
      
      Goal
      x∈ C
     *)
    clear HnxC.
    specialize (HABC x).                    (* !!!! *)
    apply HABC.
    now split.
  Qed.

  (*
    Example 3.2.5. Suppose that A ⊆ B, a ∈ A, and a / ∈ B \ C. Prove that a ∈ C.
   *)

  
  Lemma ex3_2_5 A B C : A ⊆ B -> forall a, a ∈ A /\ ~ a ∈ B \ C -> a ∈ C.
  Proof.
    intros HAB a [HaA H].
    apply NNPP.
    intros HnaC.
    apply H.
    split.
    - specialize (HAB a).
      apply HAB.
      now apply HaA.
    - easy.
  Qed.
  
  (* 集合演算を論理式に変換する補題 *)
  (* Vanilla Coqだと、「<->」 の扱いが面倒だが。 *)
  
  Lemma l_nn P Q : (P <-> Q) <-> (~ P <-> ~ Q).
  Proof.
    split.
    - intros H.
      split.
      + intro HnP.
        intro HQ.
        apply HnP.
        now apply H.
      + intro HnQ.
        intro HP.
        apply HnQ.
        now apply H.
    - intros H.
      split.
      + intros HP.
        apply NNPP.
        intro HnQ.
        now apply H in HnQ.
      + intros HQ.
        apply NNPP.
        intro HnP.
        now apply H in HnP.
  Qed.
  
  Lemma l_union A B : forall a, a ∈ A ∪ B <-> a ∈ A \/ a ∈ B.
  Proof.
    intro a.
    split.
    - intros [x H1 | x H2].
      + now left.
      + now right.
    - intros [H1 | H2].
      + now apply Union_introl.
      + now apply Union_intror.
  Qed.
  
  Lemma ln_union A B : forall a, ~ a ∈ A ∪ B <-> ~ (a ∈ A \/ a ∈ B).
  Proof.
    intros a.
    assert ((a ∈ A ∪ B <-> a ∈ A \/ a ∈ B) <->
            (~ a ∈ A ∪ B <-> ~ (a ∈ A \/ a ∈ B))) as Hnn by apply l_nn.
    apply Hnn.
    now apply l_union.
  Qed.
  
  Lemma l_inter A B : forall a, a ∈ A ∩ B <-> a ∈ A /\ a ∈ B.
  Proof.
    intro a.
    split.
    - intros [x H1 H2].
      + now split.
    - intros [H1 H2].
      now apply Intersection_intro.
  Qed.
  
  Lemma ln_inter A B : forall a, ~ a ∈ A ∩ B <-> ~ (a ∈ A /\ a ∈ B).
  Proof.
    intros a.
    assert ((a ∈ A ∩ B <-> a ∈ A /\ a ∈ B) <->
            (~ a ∈ A ∩ B <-> ~ (a ∈ A /\ a ∈ B))) as Hnn by apply l_nn.
    apply Hnn.
    now apply l_inter.
  Qed.
  
  Lemma l_subs A B : forall a, a ∈ A \ B <-> a ∈ A /\ ~ a ∈ B.
  Proof.
    split.
    - intros [HaA HnaB].
      now split.
    - intros [HaA HnaB].
      now split.
  Qed.

  Lemma ln_subs A B : forall a, ~ a ∈ A \ B <-> ~ (a ∈ A /\ ~ a ∈ B).
  Proof.
    intros a.
    assert ((a ∈ A \ B <-> a ∈ A /\ ~ a ∈ B) <->
            (~ a ∈ A \ B <-> ~ (a ∈ A /\ ~ a ∈ B))) as Hnn by apply l_nn.
    apply Hnn.
    now apply l_subs.
  Qed.
  
  Lemma l_seteq A B : (A ⊆ B /\ B ⊆ A) <-> A = B.
  Proof.
    split.
    - intros [HAB HBA].
      apply Extensionality_Ensembles.
      unfold Same_set.
      now split.
    - intro H.
      now rewrite H.
  Qed.
  
  (* l_union を使うことで、apply Union_introl などを直接使う必要はなくなる。 *)
  Lemma union_id A : A ∪ A = A.
  Proof.
    apply l_seteq.
    split.
    - intros x HAA.
      apply l_union in HAA.
      now destruct HAA.
    - intros x HA.
      apply l_union.
      now left.
  Qed.
  
  Lemma ex3_2_1' A B C : forall a, A ∩ C ⊆ B /\ a ∈ C -> ~ a ∈ A \ B.
  Proof.
    intros a [HAC HaC].
    specialize (HAC a).
    apply ln_subs.
    intro H.
    destruct H as [HaA HnaB].
    apply HnaB.
    apply HAC.
    apply l_inter.
    now split.
  Qed.
  
  Lemma ex3_2_3' A B C : A \ B ⊆ C -> forall x, x ∈ A \ C -> x ∈ B.
  Proof.
    intros HABC x HxAC.
    specialize (HABC x).
    assert (x ∈ A \ C -> x ∈ A /\ ~ x ∈ C) by apply l_subs.
    apply H in HxAC ; clear H.
    destruct HxAC as [HxA HnxC].
    apply NNPP.
    intros HnxB.
    apply HnxC.
    apply HABC.
    apply l_subs.
    now split.
  Qed.
  
  Lemma ex3_2_5' A B C : A ⊆ B -> forall a, a ∈ A /\ ~ a ∈ B \ C -> a ∈ C.
  Proof.
    intros HAB a [HaA H].
    apply NNPP.
    intros HnaC.
    apply H.
    specialize (HAB a).
    apply l_subs.
    split.
    - apply HAB.
      now apply HaA.
    - easy.
  Qed.
  
End Sets.

(* END *)
