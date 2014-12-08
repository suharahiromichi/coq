(**
Coqでの形式化された不完全性定理の証明
========

2014/12/08 @suharahiromichi

この文章のソースコードは以下にあります。

https://github.com/suharahiromichi/coq/blob/master/tit/tit_formal.v
 *)

(**
# はじめに

菊池誠さん著「不完全性定理」共立出版 2014 の 7.4節と7.5節の形式化された
第一不完全性定理と第二不完全性定理の証明をCoq SSReflectに写してみた。

原則として説明は省くので、必要に応じてオリジナルを参照してください。
*)

Require Import ssreflect ssrbool eqtype ssrnat.

(**
# 準備

## 古典論理の公理

全体に、排中律や二重否定除去を使用するので、古典論理をインポートする。
*)

Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.Classical.
Check classic.                              (* forall P : Prop, P \/ ~ P *)
Check not_not.                              (* forall P : Prop, ~ ~ P -> P *)

(**
## 命題論理の公理

2.3節で導入された「命題論理の公理」をCoqの枠組みの中で証明しておく。
*)

Lemma Ax1 {φ ψ : Prop} : φ -> (ψ -> φ).
Proof.
  move=> Hpai Hpsi.
  by apply: Hpai.
Qed.

Lemma Ax2 {φ ψ ρ : Prop} : (φ -> (ψ -> ρ)) -> ((φ -> ψ) -> (φ -> ρ)).
Proof.
  move=> H1 H2 Hpai.
  apply: H1.
  - by apply: Hpai.
  - by apply H2, Hpai.
Qed.

Lemma Ax3 {φ ψ : Prop} : (~ φ -> ~ ψ) -> (ψ -> φ).
Proof.
  apply contrapositive.
  - by apply: classic.
Qed.

(**
対偶については、他の組み合わせも証明しておく。
 *)
Lemma Ax3' (φ ψ : Prop) : (φ -> ψ) -> (~ ψ -> ~ φ).
Proof.
  move=> H Hnpai Hpsi.
  by apply Hnpai, H, Hpsi.
Qed.

Lemma Ax3'' (φ ψ : Prop) : (φ -> ~ ψ) -> (ψ -> ~ φ).
Proof.
  move=> H Hpsi Hpai.
  by apply H in Hpai.
Qed.

Lemma Ax3''' (φ ψ : Prop) : (~ φ -> ψ) -> (~ ψ -> φ).
Proof.
  move=> H.
  apply: Ax3 => Hnpai Hnpsi.
  by apply Hnpsi, H, Hnpai.
Qed.

(*
Variable model theory : Set.
Variable T : theory.
Variable v : model.
Variable assertion : theory -> Prop -> Prop.
Variable models : model -> Prop -> Prop.
Notation "T ⊦ φ" := (assertion T φ) (at level 100, no associativity).
Notation "v ⊧ φ" := (models v φ) (at level 100, no associativity).
*)

(**
## 可導性条件

7.4節で導入された可導性条件を公理として定義する。
本資料ではここを形式化の出発点とする。

また、公理と定理は T ⊦ φ の形なので、Tは省略する。
*)
Variable enc : Prop -> nat.
Notation "⌜ φ ⌝" := (enc φ) (at level 9, no associativity).
Variable PrT : nat -> Prop.

(* φをΣ1文とすると、Σ1完全性から、T ⊦ φ -> PrT ⌜φ⌝ となる(定理7.4.4)。 *)
Axiom D1 : forall {φ : Prop}, φ -> PrT ⌜φ⌝. (* 定理7.4.4 *)
Axiom D2 : forall {φ ψ : Prop}, (PrT ⌜φ -> ψ⌝) -> PrT ⌜φ⌝ -> PrT ⌜ψ⌝.
Axiom D3 : forall {φ : Prop}, PrT ⌜φ⌝ -> PrT ⌜(PrT ⌜φ⌝)⌝.

Lemma L7_4_3 (φ ψ : Prop) : (φ -> ψ) -> PrT ⌜φ⌝ -> PrT ⌜ψ⌝.
Proof.
  move=> H.
  by apply D2, D1, H.
Qed.

Lemma L7_5_3 (φ : Prop) :
  (PrT ⌜φ⌝ -> PrT ⌜~ φ⌝) -> (PrT ⌜φ⌝ -> PrT ⌜0 = 1⌝).
Proof.
  Check (@Ax2 (PrT ⌜~ φ⌝) (PrT ⌜0 = 1⌝)).
  apply: Ax2 => H.
  apply: D2.
  have Hcontra : φ -> (~ φ -> 0 = 1) by [].
  apply L7_4_3 in Hcontra.
  apply Hcontra.
  by apply H.
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
  by apply H.
Qed.

(**
# 第一不完全性定理

## ゲーデル文
 *)

Variable σ : Prop.
Axiom G : σ <-> ~ PrT ⌜σ⌝.
Definition Con := ~ PrT ⌜0 = 1⌝.

(**
## 第一不完全性定理 (1)
*)
Theorem T7_5_5_1 : Con -> ~ PrT ⌜σ⌝.
Proof.
  have G' : PrT ⌜σ⌝ -> ~ σ.
  - move=> G2 Gsigma.
    apply G in Gsigma.
    apply Gsigma.
    by apply: G2.
  apply: Ax3'.
  apply: L7_5_3.
  move/D3.
  by apply L7_4_3, G'.
Qed.

(**
## 第一不完全性定理 (2)
*)
Theorem T7_5_5_2 :
  (PrT ⌜(PrT ⌜σ⌝)⌝ -> PrT ⌜σ⌝) /\ Con -> ~ PrT ⌜~ σ⌝.
Proof.
  case=> H.
  apply Ax3 => H1.
  apply not_not in H1.
  - apply.
    apply (L7_5_4 σ).
    + move=> H2.
      have G' : ~ σ -> PrT ⌜σ ⌝ by apply Ax3''' => /G.
      apply (L7_4_3 (~ σ) (PrT ⌜σ⌝)) in G'.
      apply H, G'.
      by apply H1.
    + by apply H1.
  - by apply classic.
Qed.

(**
# 第二不完全性定理
 *)

Lemma encoding (φ ψ : Prop) :
  (φ <-> ψ) -> (PrT ⌜φ⌝ -> PrT ⌜ψ⌝).
Proof.
  move=> H H0.
  case H.
  move=> H1 H2.
  apply D1, (@D2 φ ψ) in H1.
  - by apply H1.
  - by apply (@D2 φ ψ) in H1; apply H0.
Qed.    

Lemma L7_5_8 :  Con <-> σ.
Proof.
  split.
  (* -> *)
  - move=> H.
    apply G.
    by apply T7_5_5_1 in H.
  (* <- *)
  - move/G.
    apply Ax3'.
    by apply L7_4_3.
Qed.

Theorem T7_5_13 : Con -> ~ PrT ⌜Con⌝.
Proof.
  apply Ax3'.
  move/(encoding  Con σ L7_5_8).
  apply Ax3.
  by apply T7_5_5_1.
Qed.

(* END *)
