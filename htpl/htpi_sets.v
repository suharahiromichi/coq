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

  (*
    Example 3.3.1. Suppose A, B, and C are sets, and A \ B ⊆ C.
    Prove that A \ C ⊆ B.
   *)

  Lemma ex3_3_1 A B C : A \ B ⊆ C -> A \ C ⊆ B.
  Proof.
    intros H x.
    (*
    Givens
    A\B ⊆ C
    
    Goal
    x ∈ A\C → x ∈ B
     *)
    now apply ex3_2_3.
  Qed.
  
  (*
    Example 3.3.2. Suppose A and B are sets.
    Prove that if A ∩ B = A then A ⊆ B.
   *)

  Lemma ex3_3_2 A B : A ∩ B = A -> A ⊆ B.
  Proof.
    intros HAB x HA.
    (*
      Givens
      A∩B=A
      x∈A
  
      Goal 
      x∈B 
     *)
    rewrite <- HAB in HA.
    now destruct HA.
  Qed.
  
  (* 集合族 *)

  Variable K : Type.
  Definition Fam := K -> Shugo.
  
  Inductive UnionF (F : Fam) : Shugo :=
    unionf_intro : forall x : U, (exists n : K, x ∈ F n) -> x ∈ UnionF F.
  
  Inductive InterF (X : Fam) : Shugo :=
    interf_intro : forall x : U, (forall n : K, x ∈ X n) -> x ∈ InterF X.
  
  Definition InF (F : Fam) (A : Shugo) : Prop := exists n, F n = A.
  
  (*
    Example 3.3.4. Suppose F and G are families of sets and F ∩ G ≠ ø.
    Prove that ∩F ⊆ ∪G.
   *)
  
  Lemma ex3_3_4 F G : (exists A, InF F A /\ InF G A) -> InterF F ⊆ UnionF G.
  Proof.
    intros HFG x H.
    (*
      Givens
      ∃A(A ∈ F ∩ G)
      ∀A ∈ F(x ∈ A)
      
      Goal
      ∃A ∈ G(x ∈ A)
     *)
    (*  destruct HFG as [A [[n HF] [m HG]]]. *)
    destruct HFG as [A0 [HF HG]].
    destruct H as [x H].
    apply unionf_intro.
    (*
      Givens
      A0 ∈ F
      A0 ∈ G
      ∀A ∈ F(x ∈ A)
      
      Goal
      ∃A ∈ G(x ∈ A)
     *)
    destruct HF as [n HF].
    destruct HG as [m HG].
    specialize (H n).
    exists m.
    rewrite HF in H.
    now rewrite HG.
  Qed.
  
  (* 予備 *)
  (* 集合族 F G について、 F ∩ G を定義していないので、次を使う。 *)
  Goal forall F G, (exists A, InF F A /\ InF G A) <-> (exists n m, F n = G m).
  Proof.
    split.
    - intros [A [[n HF] [m HG]]].
      exists n, m.
      now rewrite HF, HG.
    - intros [n [m H]].
      exists (G m).
      split.
      + rewrite <- H.
        now exists n.
      + rewrite <- H.
        now exists m.
  Qed.
  
  (*
    Example 3.3.5. Suppose B is a set and F is a family of sets.
    Prove that if ∪F ⊆ B then F ⊆ Power(B).
    
    Power(B) はBの冪集合で、部分集合の全体である。
    
    F ⊆ Power(B)
    <->
    ∀x(x ∈ F → x ∈ Power(B)) ........... xはBの部分集合である。
    <->
    ∀x(x ∈ F → ∀y(y ∈ x -> y ∈ B))
   *)
  
  (*
    Givens
    ∪F ⊆ B
    x ∈ F ....... x は 集合族Fの適当な要素 ∃n(x = F n)
    y ∈ x
    
    Goal
    y ∈ B
   *)

  Lemma ex3_3_5 : forall (F : Fam) (B x : Shugo) (y : U),
      UnionF F ⊆ B -> InF F x -> y ∈ x -> y ∈ B.
  Proof.
    intros F B x y Hun Hin Hyn.
    specialize (Hun y).
    apply Hun.
    (*
      Givens
      ∪F ⊆ B
      x ∈ F
      y ∈ x
      
      Goal
      y ∈ ∪F
     *)
    apply unionf_intro.
    destruct Hin as [n Hin].
    exists n.
    now rewrite Hin.
  Qed.
  
  (*
    Example 3.4.1. Suppose A ⊆ B, and A and C are disjoint.
    Prove that A ⊆ B \ C.
   *)
  
  Lemma not_in_empty : forall x, ~ x ∈ ø.
  Proof.
    intros x Hc.
    (* unfold In in Hc. *)
    destruct Hc.
  Qed.
  
  Lemma inter_empty A B : A ∩ B = ø -> ~ exists y, y ∈ A /\ y ∈ B.
  Proof.
    intros HAB [y [HA HB]].
    apply l_seteq in HAB as [H1 H2].
    specialize (H1 y).
    specialize (H2 y).
    apply (not_in_empty y).                 (* y ∈ ø *)
    apply H1.
    now split.
  Qed.
  
  Lemma ex3_4_1 A B C : A ⊆ B -> A ∩ C = ø -> A ⊆ B \ C.
  Proof.
    intros HAB H x HA.
    split.
    (* 
       Givens
       A ∩ C = ∅
       x ∈ A
       
       Goals
       x ∈ B
       ~ x ∈ C
     *)
    - specialize (HAB x).
      now apply HAB.
    - intros Hc.
      apply inter_empty in H.
      apply H.
      now exists x.
  Qed.
  
  (*
    Example 3.4.4. Suppose A, B, and C are sets.
    Prove that A ∩ (B \ C) = (A ∩ B) \ C.
   *)

  Lemma ex3_4_4_sub_1 A B C : (forall x, x ∈ A ∩ (B \ C)) <->
                              (forall x, x ∈ A /\ x ∈ B /\ ~x ∈ C).
  Proof.
    split.
    - intros H x.
      specialize (H x).
      destruct H as [x H1 [H2 H3]].
      easy.
    - intros H x.
      specialize (H x).
      now split; [| split].
  Qed.
  
  Lemma ex3_4_4_sub_2 A B C : (forall x, x ∈ (A ∩ B) \ C) <->
                              (forall x, x ∈ A /\ x ∈ B /\ ~x ∈ C).
  Proof.
    split.
    - intros H x.
      specialize (H x).
      destruct H as [[H1 H2] H3].
      easy.
    - intros H x.
      specialize (H x).
      now split; [split |].
  Qed.

  Lemma ex_3_4_4 A B C : (forall x, x ∈ A ∩ (B \ C)) <->
                         (forall x, x ∈ (A ∩ B) \ C).
  Proof.
    split; intro H.
    - apply ex3_4_4_sub_2.
      now apply ex3_4_4_sub_1.
    - apply ex3_4_4_sub_1.
      now apply ex3_4_4_sub_2.
  Qed.
  
  (*
    Example 3.5.1. Suppose that A, B, and C are sets. Prove that if A ⊆ C and
    B ⊆ C then A ∪ B ⊆ C.
  *)
  Lemma ex3_5_1 A B C : A ⊆ C -> B ⊆ C -> A ∪ B ⊆ C.
  Proof.
    intros HAC HBC x H.
    destruct H as [x HxA | x HxB].
    (*
      Case 1:
      Givens
      A ⊆ C
      B ⊆ C 
      x ∈ A
      Goal
      x ∈ C
     *)
    - specialize (HAC x).
      now apply HAC.
    (*
      Case 2:
      Givens
      A ⊆ C
      B ⊆ C
      x ∈ B
      Goal
      x ∈ C
     *)
    - specialize (HBC x).
      now apply HBC.
  Qed.
  
  (*
    Example 3.5.2. Suppose that A, B and C are sets.
    Prove that A \ (B \ C) ⊆ (A \ B) ∪ C.
   *)

  Lemma not_and_1_or P Q : ~ (P /\ ~ Q) -> ~ P \/ Q.
    intros H.
    Check not_and_or.
    apply not_and_or in H.
    destruct H as [HP | HQ].
    - now left.
    - apply NNPP in HQ.
      now right.
  Qed.
  
  Lemma ex3_5_2 A B C : A \ (B \ C) ⊆ (A \ B) ∪ C.
  Proof.
    intros x H.
    destruct H as [H1 H2].
    assert (~ x ∈ B \ C -> ~ (x ∈ B /\ ~ x ∈ C)) as H by apply ln_subs.
    apply H in H2. clear H.
    apply not_and_1_or in H2.
    apply l_union.
    destruct H2.
    (*
      case 1:
      Givens
      x ∈ A
      ~ x ∈ B
      Goal
      ( x ∈ A ∧ ~ x ∈ B ) ∨ x ∈ C
     *)
    - left.
      apply l_subs.
      now split.
    (*
      case 2:
      Givens
      x ∈ A
      x ∈ C
      Goal
      ( x ∈ A ∧ ~ x ∈ B ) ∨ x ∈ C
     *)
    - now right.
  Qed.
  
  (*
    Example 3.6.2. Prove that there is a unique set A such that for every set B,
    A ∪ B = B.
    
    Example 3.6.1 で証明した：
    ∃!P(x) <->
    ∃xP(x) ∧ ∀y∀z((P(y) ∧ P(z)) → y = z)
    を使う。
    
    ∃!A.∀B.A ∪ B = B
    <->
    ∃A. ∀B.A ∪ B = B
    /\
    ∀C∀D(∀B.(C ∪ B = B) /\ ∀B.(D ∪ B = B)) → C = D).
   *)
  
  Lemma union_comm A B : A ∪ B = B ∪ A.
  Proof.
    apply l_seteq.
    split.
    - intros x HxAB.
      destruct HxAB.
      + apply l_union. now right.
      + apply l_union. now left.
    - intros x HxBA.
      destruct HxBA.
      + apply l_union. now right.
      + apply l_union. now left.
  Qed.
  
  Lemma ex3_6_2 : (exists A, forall B, A ∪ B = B) /\
                  forall C D, (forall B, C ∪ B = B) /\ (forall B, D ∪ B = B) -> C = D.
  Proof.
    split.
    - exists ø.
      intros B.
      apply l_seteq.
      split; intros x H.
      + now destruct H.
      + apply l_union. now right.
    - intros C D [HC HD].
      (*
        Givens
        ∀B(C ∪ B = B)
        ∀B(D ∪ B = B)
        Goal
        C = D
       *)
      specialize (HC D).
      specialize (HD C).
      rewrite <- HC.
      rewrite <- HD at 1.
      now rewrite union_comm.
  Qed.
  
  (*
    Example 3.6.4. Suppose A, B, and C are sets, A and B are not disjoint,
    A and C are not disjoint, and A has exactly one element.
    Prove that B and C are not disjoint.
   *)

  (*
    Givens
    A ∩ B <> ∅
    A ∩ C <> ∅
    ∃!x(x ∈ A)
    Goal
    B ∩ C <> ∅
   *)
  
  Lemma not_empty__exists A : A <> ø <-> exists x, x ∈ A.
  Proof.
    split.
    - intro Hc.
      apply NNPP.
      intros H1.
      apply Hc.
      apply l_seteq.
      split.
      + intros x H2.
        exfalso.
        apply H1.
        now exists x.
      + easy.
    - intros H.
      destruct H as [x H].
      intros Hc.
      rewrite Hc in H.
      easy.
  Qed.
  
  Lemma ex3_6_4 A B C : A ∩ B <> ø -> A ∩ C <> ø ->
                        (exists x, x ∈ A) -> (* 使わない *)
                        (forall y z, y ∈ A /\ z ∈ A -> y = z) ->
                        B ∩ C <> ø.
  Proof.
    intros HAB HAC HxA H.
    apply not_empty__exists in HAB.
    apply not_empty__exists in HAC.
    apply not_empty__exists.
    (*
      Givens
      ∃x(x ∈ A ∧ x ∈ B)
      ∃x(x ∈ A ∧ x ∈ C)
      ∃x(x ∈ A)
      ∀y∀z((y ∈ A ∧ z ∈ A) → y = z)
      Goal
      ∃x(x ∈ B ∧ x ∈ C)
     *)
    destruct HAB as [x [b HbA HbB]].
    destruct HAC as [y [c HcA HcB]].
    specialize (H b c).
    (* 
       Givnes
       b ∈ A
       b ∈ B
       c ∈ A
       c ∈ C
       b ∈ A /\ c ∈ A -> b = c
       Goal
       exists x0, x0 ∈ B ∩ C
     *)
    (* 
       Givnes
       b ∈ B
       c ∈ C
       b = c
       Goal
       b ∈ B
       b ∈ C
     *)
    exists b.
    apply l_inter.
    split.
    - easy.
    - rewrite H.
      + easy.
      + easy.
  Qed.
  
End Sets.

(* END *)
