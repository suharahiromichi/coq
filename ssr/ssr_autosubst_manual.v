(**
https://www.ps.uni-saarland.de/autosubst/doc/manual.pdf
*)

(*
以下を同じディレクトリに置いて、
Autosubst.v  Lib.v  MMap.v  <このファイル>
coq_makefile *.v > Makefile
*)

Require Import Autosubst.                   (* これだけでよい。 *)
Require Import Relations.
Require Import Relation_Operators.          (* rt1n_trans が上書きされぬよう。 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. (* SSReflect *)

(**
# Tutorial
*)
(**
Figure 4: Declaration of the syntax of System F
*)
Inductive type : Type :=
| TyVar (x : var)
| Arr (A B : type)
| All (A : {bind type}).

Inductive term :=
| Var (x : var)
| Abs (A : type) (s : {bind term})
| App (s t : term)
| TAbs (s : {bind type in term})
| TApp (s : term) (A : type).

Instance VarConstr_type : VarConstr type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_type : SubstLemmas type. derive. Qed.
Instance HSubst_term : HSubst type term. derive. Defined.
Instance VarConstr_term : VarConstr term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed.
Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Section SubstLemmas.
Variables (x : var) (s : type).
Variables (σ  τ: var -> type).            (* 代入 *)
Variables (ξ : var -> var).
Variables (Δ : type -> type).

(* autosubst で解けるようになる命題 (Figure.3) *)
Goal s.[σ].[τ] = s.[σ >> τ]. Proof. apply (subst_comp s σ τ). Qed.
Goal s.[Autosubst.Var] = s. Proof. apply (subst_id s). Qed.
Goal (Autosubst.Var x).[σ] = σ x. Proof. apply (id_subst x σ). Qed.
Goal rename ξ s = s.[ren ξ]. Proof. apply (rename_subst ξ s). Qed.

Check ren.                                  (* (var -> var) -> var -> term *)
Check rename.                               (* (var -> var) -> type -> type *)
Goal (TyVar 0).[σ] = σ 0. Proof. auto. Qed.
End SubstLemmas.

(**
## Small Step Reduction (System F)
*)

Inductive step : term -> term -> Prop :=
| Step_Beta A s s' t : s' = s.[t .: Autosubst.Var] -> step (App (Abs A s) t) s'
| Step_TBeta B s s' : s' = s.|[B .: Autosubst.Var] -> step (TApp (TAbs s) B) s'
| Step_App1 s s' t: step s s' -> step (App s t) (App s' t)
| Step_App2 s t t': step t t' -> step (App s t) (App s t')
| Step_Abs A s s' : step s s' -> step (Abs A s) (Abs A s').

Section Test_Stream.
Variable a : term.
Variable f : var -> term.

Goal (a .: f) 0 = a. Proof. auto. Qed.
Goal (a .: f) 1 = f 0. Proof. auto. Qed.

Goal (Var 0).[(a .: f)] = a. Proof. auto. Qed.
Goal (Var 1).[(a .: f)] = (Var 0).[f]. Proof. auto. Qed.
End Test_Stream.

Lemma step_subst s s' : step s s' -> forall σ, step s.[σ] s'.[σ].
Proof. induction 1; constructor; subst; autosubst. Qed.


(**
## 型付け (型付きラムダ式)
*)
Inductive ty (Γ : var -> type) : term -> type -> Prop :=
| Ty_Var x A : Γ x = A -> ty Γ (Var x) A
| Ty_Abs s A B : ty (A .: Γ) s B -> ty Γ (Abs A s) (Arr A B)
| Ty_App s t A B : ty Γ s (Arr A B) -> ty Γ t A ->  ty  Γ (App s t) B.

Lemma ty_ren Γ s A : ty Γ s A ->
                      forall Δ ξ, Γ = (ξ >>> Δ) ->
                                    ty Δ s.[ren ξ] A.
  Proof.
    induction 1; intros; subst; autosubst; econstructor; eauto.
    - eapply IHty. autosubst.
Qed.                                     

Lemma ty_subst Γ s A: ty Γ s A ->
                       forall σ Δ, (forall x, ty Δ (σ x) (Γ x)) ->
                                     ty Δ s.[σ] A.
Proof.
  induction 1; intros; subst; autosubst; eauto using ty.
  - econstructor. eapply IHty.
    intros [|] *; autosubst; eauto using ty, ty_ren.
Qed.

Lemma ty_pres Γ s A : ty Γ s A ->
                       forall s', step s s' ->
                                  ty Γ s' A.
Proof.
  induction 1; intros s' H_step; autosubst;
  inversion H_step; ainv; eauto using ty.
  - eapply ty_subst; try eassumption.
    intros [|]; simpl; eauto using ty.
Qed.



Section Defined_Operation.
Variables (x : var) (s : type).
Variables (σ  τ: var -> type).            (* 代入 *)
Variables (ξ : var -> var).
Variables (Δ : type -> type).

(* 諸定義 *)
Goal s.[σ] = subst σ s. Proof. auto. Qed.
Goal (σ >>> Δ) x = Δ (σ x). Proof. auto. Qed.
Goal σ >> τ = σ >>> (subst τ). Proof. auto. Qed.
End Defined_Operation.



(* END *)
