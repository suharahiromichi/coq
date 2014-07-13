(**
Autosubst Manual
https://www.ps.uni-saarland.de/autosubst/doc/manual.pdf

第1章の Tutorial をもとに、STLC（単純型付きラムダ計算）の型の保存性を証明する。
*)

(*
使い方（これは、Autosubstのバージョンアップで変わるので、注意すること）
以下を同じディレクトリに置いて、
Autosubst.v  Lib.v  MMap.v  <このファイル>
coq_makefile *.v > Makefile
*)

Require Import Autosubst. (* MMap. *)
(*
Require Import Relations.
Require Import Relation_Operators.          (* rt1n_trans が上書きされぬよう。 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. (* SSReflect *)
*)

(**
Defining the Syntax
*)
Inductive type : Type :=
| Base
| Arr (A B : type).

Inductive term :=
| Var (x : var)
| Abs (A : type) (s : {bind term})
| App (s t : term).

(**
Generating the Operation
 *)
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance HSubst_term : HSubst type term. derive. Defined.
Instance VarConstr_term : VarConstr term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(**
## Small Step Reduction STLC
*)
Inductive step : term -> term -> Prop :=
| Step_Beta A s s' t : s' = s.[t .: Autosubst.Var] -> step (App (Abs A s) t) s'
| Step_App1 s s' t: step s s' -> step (App s t) (App s' t)
| Step_App2 s t t': step t t' -> step (App s t) (App s t')
| Step_Abs A s s' : step s s' -> step (Abs A s) (Abs A s').

(**
## 型付け STLC
*)
Inductive ty (Γ : var -> type) : term -> type -> Prop :=
| Ty_Var x A : Γ x = A -> ty Γ (Var x) A
| Ty_Abs s A B : ty (A .: Γ) s B -> ty Γ (Abs A s) (Arr A B)
| Ty_App s t A B : ty Γ s (Arr A B) -> ty Γ t A ->  ty  Γ (App s t) B.

(**
### 補題

型付けのコンテキストΓを、コンテキストΔとリネーム規則ξにわける方法を示す。
 *)
Lemma ty_ren (Γ : var -> type) (s : term) (A : type) :
  ty Γ s A ->
  forall (Δ : var -> type) (ξ : var -> var),
    Γ = (ξ >>> Δ) -> ty Δ s.[ren ξ] A.
Proof.
    induction 1; intros; subst; autosubst; econstructor; eauto.
    - eapply IHty. autosubst.
Qed.                                     

(**
### 置換補題(Substitution Lemma)?

Γのもとで項sがAの型を持つとする。
すべての変数xについて、Δのもとで、σで置き換えた項(σ x)が、Γで置き換えた型(Γ x)を持つならば、
Δのもとで、項sにσで置換した項は、型Aを持つ。
つまり、項sから型Aを保ちながら、別の項(s.[σ])を作る方法を示す。
*)
Lemma ty_subst (Γ : var -> type) (s : term) (A : type) :
  ty Γ s A ->
  forall (σ : var -> term) (Δ : var -> type),
    (forall x, ty Δ (σ x) (Γ x)) -> ty Δ s.[σ] A.
Proof.
  induction 1; intros; subst; autosubst; eauto using ty.
  - econstructor. eapply IHty.
    intros [|] *; autosubst; eauto using ty, ty_ren.
Qed.

(**
### 型の保存性の定理
 *)
Lemma ty_pres (Γ : var -> type) (s : term) (A : type) :
  ty Γ s A ->
  forall (s' : term), step s s' -> ty Γ s' A.
Proof.
  induction 1; intros s' H_step; autosubst;
  inversion H_step; ainv; eauto using ty.
  - eapply ty_subst; try eassumption.
    intros [|]; simpl; eauto using ty.
Qed.

(* END *)
