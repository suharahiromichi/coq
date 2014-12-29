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
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  - by apply: H2; apply: Hpai.
Qed.

Lemma Ax3 {φ ψ : Prop} : (~ φ -> ~ ψ) -> (ψ -> φ).
Proof.
  apply contrapositive.
  - by apply: classic.
Qed.

(**
対偶については、他の組み合わせも証明しておく。
 *)
Lemma Ax31 (φ ψ : Prop) : (φ -> ψ) -> (~ ψ -> ~ φ).
Proof.
  move=> H Hnpai Hpsi.
  by apply: Hnpai; apply: H; apply: Hpsi.
Qed.

Lemma Ax32 (φ ψ : Prop) : (φ -> ~ ψ) -> (ψ -> ~ φ).
Proof.
  by move=> H /H.
Qed.

Lemma Ax33 (φ ψ : Prop) : (~ φ -> ψ) -> (~ ψ -> φ).
Proof.
  move=> H.
  apply: Ax3 => Hnpai Hnpsi.
  by apply: Hnpsi; apply: H; apply: Hnpai.
Qed.

(*
以下は使用しない：

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

本資料では、7.4節で導入された可動性条件を出発点とする。

- 言語Lを、算術の言語 LA={0,1,+,・,≦} を含み、ゲーデル数化を伴う言語とする。
- 理論Tを、ペアノ算術を含む言語Lの理論とする。


理論Tの上で、次のD1,D2,D3が成立するものとする。ただし、


- ⌜φ⌝は、論理式φのゲーデル数化（エンコード）した自然数を示す。
- PrT(x)は、自然数xに対する、論理Tで証明のある論理式を示す。
*)

Variable enc : Prop -> nat.
Notation "⌜ φ ⌝" := (enc φ) (at level 9, no associativity).
Variable PrT : nat -> Prop.

Axiom D1' : forall {φ : Prop}, φ -> PrT ⌜φ⌝. (* 注意 *)
Axiom D2 : forall {φ ψ : Prop}, (PrT ⌜φ -> ψ⌝) -> PrT ⌜φ⌝ -> PrT ⌜ψ⌝.
Axiom D3 : forall {φ : Prop}, PrT ⌜φ⌝ -> PrT ⌜(PrT ⌜φ⌝)⌝.

(**
注意：
D1 は、正しくは、「T ⊦ φ ならば T ⊦ PrT(⌜φ⌝)」 であり、
これを形式化したものは、D3であって D1' ではない。
D1' のは、φをΣ1論理式に制限しないと成立しない（定理7.4.4）。
そのため、この記述は不正確であり、見直す必要がある。
*)

Lemma L7_4_3 (φ ψ : Prop) : (φ -> ψ) -> PrT ⌜φ⌝ -> PrT ⌜ψ⌝.
Proof.
  move=> H.
  by apply: D2; apply: D1'; apply: H.
Qed.

Lemma L7_5_3 (φ : Prop) :
  (PrT ⌜φ⌝ -> PrT ⌜~ φ⌝) -> (PrT ⌜φ⌝ -> PrT ⌜0 = 1⌝).
Proof.
  Check (@Ax2 (PrT ⌜~ φ⌝) (PrT ⌜0 = 1⌝)).
  apply: Ax2 => H.
  apply: D2.
  have Hcontra : φ -> (~ φ -> 0 = 1) by [].
  move/L7_4_3 in Hcontra.
  apply: Hcontra.
  by apply: H.
Qed.

Lemma L7_5_4 (φ : Prop) :
  (PrT ⌜~ φ⌝ -> PrT ⌜φ⌝) -> (PrT ⌜~ φ⌝ -> PrT ⌜0 = 1⌝).
Proof.
  apply: Ax2.
  move=> H.
  apply: D2.
  have Hcontra : ~ φ -> (φ -> 0 = 1) by [].
  move/L7_4_3 in Hcontra.
  apply Hcontra.
  by apply H.
Qed.

(**
# ゲーデル文と無矛盾性をあらわす文
 *)

(** ゲーデル文 σ *)
Variable σ : Prop.

(** ゲーデル文の満たす性質 *)
Axiom G : σ <-> ~ PrT ⌜σ⌝.

(** 無矛盾性をあらわす文 Con *)
Definition Con := ~ PrT ⌜0 = 1⌝.

(**
# 第一不完全性定理
*)

(**
## 第一不完全性定理 (1)

Tが無矛盾ならば、σを導けない(T ⊬ σ) 。
*)
Theorem T7_5_5_1 : Con -> ~ PrT ⌜σ⌝.
Proof.
  have G' : PrT ⌜σ⌝ -> ~ σ.
  - move=> G2 /G.
    apply.
    by apply: G2.
  apply: Ax31; apply: L7_5_3.
  move/D3.
  by apply: L7_4_3; apply: G'.
Qed.

(**
## 第一不完全性定理 (2)

TがΣ1健全ならば、~σを導けない(T ⊬ ~σ) 。

ただし、「TがΣ1健全である」を以下のように弱める。

- Tが無矛盾であること(前提の/\の右のCom)、かつ、
- T ⊦ PrT ⌜σ⌝ ならば、T ⊦ σ である(前提の/\の左)。
*)
Theorem T7_5_5_2 :
  (PrT ⌜(PrT ⌜σ⌝)⌝ -> PrT ⌜σ⌝) /\ Con -> ~ PrT ⌜~ σ⌝.
Proof.
  case=> H.
  apply Ax3 => H1.
  apply not_not in H1.
  - apply.
    apply: (@L7_5_4 σ).
    + move=> H2.
      have G' : ~ σ -> PrT ⌜σ ⌝ by apply Ax33 => /G.
      * move/(@L7_4_3 (~ σ) (PrT ⌜σ⌝)) in G'.
        apply: H; apply: G'.
        by apply: H1.
    + by apply: H1.
  - by apply: classic.
Qed.

(**
# 第二不完全性定理
 *)
Lemma L7_5_8 : Con <-> σ.
Proof.
  split.
  (* -> *)
  - move=> H.
    apply G.
    by apply T7_5_5_1 in H.
  (* <- *)
  - move/G.
    apply: Ax31.
    by apply: L7_4_3.
Qed.

(**
Tが無矛盾ならは、Comを導けない(T ⊬ Com)。
*)
Theorem T7_5_13 : Con -> ~ PrT ⌜Con⌝.
Proof.
  apply: Ax31.
  have H : Con -> σ by apply L7_5_8.       (* -> だけ使う。 *)
  move/(L7_4_3 H).
  apply: Ax3.
  by apply: T7_5_5_1.
Qed.

(* END *)
