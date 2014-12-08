Require Import ssreflect ssrbool eqtype ssrnat.
Require Import Coq.Logic.Decidable.

Axiom excluded_middle : forall φ : Prop, φ \/ ~ φ.

Lemma Ax1 (φ ψ : Prop) : φ -> (ψ -> φ).
Proof.
  move=> Hpai Hpsi.
  by apply: Hpai.
Qed.

Lemma Ax2 (φ ψ ρ : Prop) : (φ -> (ψ -> ρ)) -> ((φ -> ψ) -> (φ -> ρ)).
Proof.
  move=> H1 H2 Hpai.
  apply: H1.
  - by apply: Hpai.
  - by apply: H2; apply Hpai.
Qed.

Lemma Ax3 (φ ψ : Prop) : (~ φ -> ~ ψ) -> (ψ -> φ).
Proof.
  move=> H.
  Check contrapositive.
  apply contrapositive.                     (* rewrite /decidable. *)
  - by apply: excluded_middle.
  - by apply: H.
Qed.

Lemma Ax3' (φ ψ : Prop) : (φ -> ψ) -> (~ ψ -> ~ φ).
Proof.
  move=> H Hnpsi Hpai.
  apply Hnpsi.
  apply H.
  by apply Hpai.
Qed.

Lemma Ax3'' (φ ψ : Prop) : (φ -> ~ ψ) -> (ψ -> ~ φ).
Proof.
  move=> H Hpsi Hpai.
  apply H in Hpai.
  by [].
Qed.

Lemma Ax3''' (φ ψ : Prop) : (~ φ -> ψ) -> (~ ψ -> φ).
Proof.
  move=> H.
  Check (Ax3 φ (~ ψ)).
  by [].


  admit.
Qed.

Variable model theory : Set.
Variable T : theory.
Variable v : model.
Variable assertion : theory -> Prop -> Prop.
Variable models : model -> Prop -> Prop.
Variable enc : Prop -> nat.
Notation "T ⊦ φ" := (assertion T φ) (at level 100, no associativity).
Notation "v ⊧ φ" := (models v φ) (at level 100, no associativity).
Notation "⌜ φ ⌝" := (enc φ) (at level 9, no associativity).

Variable PrT : nat -> Prop.

(* D1 を除いて T ⊦ φ の形なので、Tは取り去ってしまう。 *)

(* φをΣ1文とすると、Σ1完全性から、φ -> PrT ⌜φ⌝ となる(定理7.4.4)。 *)
Axiom D1 : forall (φ : Prop), φ -> PrT ⌜φ⌝. (* 定理7.4.4 *)
Axiom D2 : forall (φ ψ : Prop), (PrT ⌜φ -> ψ⌝) -> PrT ⌜φ⌝ -> PrT ⌜ψ⌝.
Axiom D3 : forall (φ : Prop), PrT ⌜φ⌝ -> PrT ⌜(PrT ⌜φ⌝)⌝.

Lemma L7_4_3 (φ ψ : Prop) : (φ -> ψ) -> PrT ⌜φ⌝ -> PrT ⌜ψ⌝.
Proof.
  move=> H.
  apply: D2.
  apply: D1.
  by apply H.
Qed.

Definition Con := ~ PrT ⌜0 = 1⌝.

Lemma L7_5_3 (φ : Prop) :
                    (PrT ⌜φ⌝ -> PrT ⌜~ φ⌝) -> (PrT ⌜φ⌝ -> PrT ⌜0 = 1⌝).
Proof.
  Check (Ax2 (PrT ⌜φ⌝) (PrT ⌜~ φ⌝) (PrT ⌜0 = 1⌝)).
  apply: Ax2 => H.
  apply: D2.
  have Hcontra : φ -> (~ φ -> 0 = 1) by [].
  apply L7_4_3 in Hcontra.
  apply Hcontra.
  apply H.
Qed.

Lemma L7_5_4 (φ : Prop) :
  (PrT ⌜~ φ⌝ -> PrT ⌜φ⌝) -> (PrT ⌜~ φ⌝ -> PrT ⌜0 = 1⌝).
Proof.
  apply: Ax2.
  move=> H.
  apply: D2.
  have Hcontra : ~ φ -> (φ -> 0 = 1) by [].
  apply L7_4_3 in Hcontra.
  apply Hcontra.
  apply H.
Qed.

Variable σ : Prop.
Axiom G : σ <-> ~ PrT ⌜σ⌝.

Theorem T7_5_5_1 : Con -> ~ PrT ⌜σ⌝.
Proof.
  rewrite /Con.
  apply: Ax3'.
  apply: L7_5_3 => H.
  Check (D3 σ).
  apply D3 in H.
  move: H.
  have G' : PrT ⌜σ⌝ -> ~ σ.
  - move=> G2 Gsigma.
    apply G in Gsigma.
    apply Gsigma.
      by apply: G2.
  apply: L7_4_3.
  by apply: G'.
Qed.


Axiom classic : forall P:Prop,  ~ ~ P -> P.

Theorem T7_5_5_2 :
  (PrT ⌜(PrT ⌜σ⌝)⌝ -> PrT ⌜σ⌝) /\ Con -> ~ PrT ⌜~ σ⌝.
Proof.
  rewrite /Con.
  case=> H.
  apply Ax3 => H1.
  apply classic in H1.
  move=> H2.
  apply H2.
  move {H2}.

  have G' : (PrT ⌜~ σ⌝ -> PrT ⌜σ ⌝) -> (PrT ⌜~ σ⌝ -> PrT ⌜0 = 1⌝).
  by apply L7_5_4.
  
  apply G'.
  - move=> G2.
    apply H.
    apply D3.

    have GG : ~ σ -> PrT ⌜σ ⌝.
    apply Ax3'''.
    move=> GGG.
    apply G in GGG.
    by [].

    Check L7_4_3 (~ σ) (PrT ⌜σ⌝).
    apply (L7_4_3 (~ σ) (PrT ⌜σ⌝)) in GG.
    apply H.
    apply GG.
    apply H1.
    by [].
Qed.


  have G' : (PrT ⌜PrT ⌜σ ⌝ ⌝ -> PrT ⌜σ ⌝) -> (PrT ⌜~ σ⌝ -> PrT ⌜σ⌝).
  Check L7_4_3 (~ σ) σ.
  move=> G1.
  apply (L7_4_3 (~ σ) σ).

  apply G' in H.

  apply L7_5_4 in H.


  have G' : PrT ⌜~ σ⌝ -> PrT ⌜σ⌝.
    - apply L7_4_3.
      move=> H3.
      apply G.
      move=> G2.
      apply H3.
      apply G.
      move=> G3.
      apply H2.
  move: G' H1.
  by apply L7_5_4.
Qed.

Lemma encoding (φ ψ : Prop) :
  (φ <-> ψ) -> (PrT ⌜φ⌝ -> PrT ⌜ψ⌝).
Proof.
  move=> H H0.
  case H.
  move=> H1 H2.
  apply D1 in H1.
  apply (D2 φ ψ) in H1.
  - by apply H1.
    + apply (D2 φ ψ) in H1.
      * by apply H0.
      * by apply H0.
Qed.    

Lemma L7_5_8 :  Con <-> σ.
Proof.
  split.
  - move=> H.
    apply G.
    by apply T7_5_5_1 in H.
  - move=> H.
    apply G in H.
    move: H.
    apply Ax3'.
    apply L7_4_3.
    by [].
Qed.


Theorem T7_5_13 : Con -> ~ PrT ⌜Con⌝.
Proof.
  apply Ax3' => H.
  Check encoding  Con σ L7_5_8.
  apply (encoding  Con σ L7_5_8) in H.
  move: H.
  apply Ax3 => H.
  apply T7_5_5_1.
  by [].
Qed.

(* END *)
