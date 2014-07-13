(**
Autosubst Manual
https://www.ps.uni-saarland.de/autosubst/doc/manual.pdf

これをもとに、STLC を作ってみた。Reference Manualの抄訳も含む。
System F にする途中であり、コメントで消してある。
*)

(*
使い方（これは、Autosubstのバージョンアップで変わるので、注意すること）
以下を同じディレクトリに置いて、
Autosubst.v  Lib.v  MMap.v  <このファイル>
coq_makefile *.v > Makefile
*)

Require Import Autosubst MMap.              (* MMapはいらなくなるか。 *)
Require Import Relations.
Require Import Relation_Operators.          (* rt1n_trans が上書きされぬよう。 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. (* SSReflect *)

(**
# Tutorial
*)

(**
Defining the Syntax

Figure 4: Declaration of the syntax of System F
*)
Inductive type : Type :=
| Base
(* | TyVar (x : var). *)
| Arr (A B : type).
(* | All (A : {bind type}). *)

Inductive term :=
| Var (x : var)
| Abs (A : type) (s : {bind term})
| App (s t : term).
(*
| TAbs (s : {bind type in term})
| TApp (s : term) (A : type).
*)

(**
Generating the Operation

Figure 5: Declarations to derive the operations and lemmas for STLC (* System F *)
 *)
(* Instance VarConstr_type : VarConstr type. derive. Defined. *)
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
(* Instance SubstLemmas_type : SubstLemmas type. derive. Qed. *)
Instance HSubst_term : HSubst type term. derive. Defined.
Instance VarConstr_term : VarConstr term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
(* Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed. *)
Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Section SubstLemmas_term.
Variables (x : var) (s : term).
Variables (σ  τ: var -> term).            (* 代入 *)
Variables (ξ : var -> var).

(* (Figure.3) autosubst で解けるようになる命題 term *)
Goal s.[σ].[τ] = s.[σ >> τ]. Proof. apply (subst_comp s σ τ). Qed.
Goal s.[Autosubst.Var] = s. Proof. apply (subst_id s). Qed.
Goal (Autosubst.Var x).[σ] = σ x. Proof. apply (id_subst x σ). Qed.
Goal rename ξ s = s.[ren ξ]. Proof. apply (rename_subst ξ s). Qed.
End SubstLemmas_term.

(*
Section SubstLemmas_type.
Variables (x : var) (s : type).
Variables (σ  τ: var -> type).            (* 代入 *)
Variables (ξ : var -> var).

(* (Figure.3) autosubst で解けるようになる命題 type System Fのみ。*)
Goal s.[σ].[τ] = s.[σ >> τ]. Proof. apply (subst_comp s σ τ). Qed.
Goal s.[Autosubst.Var] = s. Proof. apply (subst_id s). Qed.
Goal (Autosubst.Var x).[σ] = σ x. Proof. apply (id_subst x σ). Qed.
Goal rename ξ s = s.[ren ξ]. Proof. apply (rename_subst ξ s). Qed.
Goal (TyVar 0).[σ] = σ 0. Proof. auto. Qed. (* こちらだけ。 *)
End SubstLemmas_type.
*)

(**
## Small Step Reduction STLC (* System F *)
*)

Inductive step : term -> term -> Prop :=
| Step_Beta A s s' t : s' = s.[t .: Autosubst.Var] -> step (App (Abs A s) t) s'
(* | Step_TBeta B s s' : s' = s.|[B .: Autosubst.Var] -> step (TApp (TAbs s) B) s' *)
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
## 型付け STLC (* System F 途中 *)
*)
Inductive ty (Γ : var -> type) : term -> type -> Prop :=
| Ty_Var x A : Γ x = A -> ty Γ (Var x) A
| Ty_Abs s A B : ty (A .: Γ) s B -> ty Γ (Abs A s) (Arr A B)
| Ty_App s t A B : ty Γ s (Arr A B) -> ty Γ t A ->  ty  Γ (App s t) B.
(*
| Ty_TAbs s A : ty (Γ) s A -> ty Γ (TAbs s) (All A)  (* ????? *)
| Ty_TApp s A B : ty Γ s (All A) -> ty Γ (TApp s B) A.[B .: TyVar].
*)

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
 *)
(**
Γのもとで項sがAの型を持つとしよう。
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

(**
## 進行性の定理
*)
Inductive value : term -> Prop :=
| v_var : forall x, value (Var x)           (* Base *)
| v_abs : forall T s, value (Abs T s).      (* Arr A B *)

Lemma ty_prog (Γ : var -> type) (s : term) (A : type) :
  ty Γ s A -> value s \/ exists s', step s s'.
Proof.
  intros H; induction H.
  + left. apply v_var.
  + left. apply v_abs.
  + right. destruct IHty1.
    - destruct IHty2.
      * inversion H1; subst.
        (*  H0 : ty Γ t A *)
        (*  H2 : value t *)
        (* H : ty Γ (Var x) (Arr A B) *)
        (* H1 : value (Var x) *)
        + admit.                           (* exists s' : term, step (App (Var x) t) s' *)
        + exists (s0.[beta t]). apply Step_Beta. reflexivity.
      * destruct H2 as [t']. exists (App s t'). apply Step_App2. apply H2.
    - destruct H1 as [s']. exists (App s' t). apply Step_App1. apply H1.
Qed.

(**
# Reference Manual
 *)

(**
## Defining the Syntax （構文を定義する）
*)
(**
Figure 4を参照。

- you first have to define an inductive type of terms with de Bruijn indices. This should
  be a simple inductive definition without dependent types.
  ド・ブラウン・インデックスで項の型を定義する。これは、依存型を持たない単純な帰納的な定義であること。

- There must be at most one constructor for variables, aka de Bruijn indices. It must have
  a single argument of type var, which is a type synonym for nat.
  高々1個の変数（いわゆるド・ブラウン・インデックス）のコンストラクタがあること。それは、
  var型（natの別名）の1引数を持つこと。

- If a constructor acts as a binder for a variable of the term type T in a constructor
  argument of type U, then U has to be replaced by {bind T in U}. We can write {bind T}
  instead of {bind T in T}.
*)

(**
## Generating the Operation （substitution操作を生成する）
*)
(**
生成は。Figure 5を参照。
*)

(* Table.1 *)
Print VarConstr.                            (* fun term : Type => var -> term *)
Check Var.                                  (* var -> term *)

Print Rename.                               (* fun term : Type => (var -> var) -> term -> term *)
Check rename.                               (* (var -> var) -> term -> term *)

Print Subst.                                (* fun term : Type => (var -> term) -> term -> term *)
Check subst.                                (* (var -> term) -> term -> term *)
Locate ".[".                                (* "s .[ sigma ]" := subst sigma s *)

Print HSubst.                               (* fun inner outer : Type => (var -> inner) -> outer -> outer *)
Check hsubst.                               (* (var -> type) -> term -> term *)
Locate ".|[".                               (* s .|[ sigma ]" := hsubst sigma s *)

(* Table. 2 *)
Section GeneratingOperation_SubstLemmas_term.
Variables (x : var) (s : term).
Variables (σ  τ : var -> term).            (* 代入 *)
Variables (ξ : var -> var).

(* SubstLemmas term *)
Goal rename ξ s = s.[ren ξ]. Proof. apply (rename_subst ξ s). Qed.
Goal s.[Autosubst.Var] = s. Proof. apply (subst_id s). Qed.
Goal (Autosubst.Var x).[σ] = σ x. Proof. apply (id_subst x σ). Qed.
Goal s.[σ].[τ] = s.[σ >> τ]. Proof. apply (subst_comp s σ τ). Qed. (* Manual では >>> *)
End GeneratingOperation_SubstLemmas_term.

(*
Section GeneratingOperation_SubstLemmas_type.
Variables (x : var) (s : type).
Variables (σ  τ : var -> type).            (* 代入 *)
Variables (ξ : var -> var).

(* SubstLemmas type (System Fのみ) *)
Goal rename ξ s = s.[ren ξ]. Proof. apply (rename_subst ξ s). Qed.
Goal s.[Autosubst.Var] = s. Proof. apply (subst_id s). Qed.
Goal (Autosubst.Var x).[σ] = σ x. Proof. apply (id_subst x σ). Qed.
Goal s.[σ].[τ] = s.[σ >> τ]. Proof. apply (subst_comp s σ τ). Qed. (* Manual では >>> *)
End GeneratingOperation_SubstLemmas_type.
*)
(*
Section GeneratingOperation_HSubstLemmas_term.
Variables (x : var) (s : term).
Variables (σ  τ : var -> type).            (* 代入 *)

(* HSubstLemmas *)
Goal s.|[Autosubst.Var] = s. Proof. autosubst. reflexivity. Qed.
Goal (Autosubst.Var x).|[σ] = Autosubst.Var x. Proof. autosubst. Qed.
Goal s.|[σ].|[τ] = s.|[σ >> τ]. Proof. autosubst. Qed. (* Manual では >>> *)
End GeneratingOperation_HSubstLemmas_term.
*)
Section GeneratingOperation_SubstHSubstComp_term.
Variables (x : var) (s : term).
Variables (σ : var -> term).            (* 代入 *)
Variables (τ : var -> type).            (* 代入 *)

Check subst.                                (* (var -> term) -> term -> term *)
Check subst σ.                             (* term -> term *)
Check subst σ s.                           (* term *)
Check s.[σ].                               (* term *)
Check hsubst.                               (* (var -> type) -> term -> term *)
Check hsubst τ.                            (* term -> term *)
Check s.|[τ].                              (* term *)
Check σ >>| τ.                            (* var -> term *)
Check (s.[σ]).|[τ].
Check (s.|[τ]).[σ >>| τ].
Check (s.[σ]).|[τ] = (s.|[τ]).[σ >>| τ]. (* 括弧は省略できる。 *)

Goal s.[σ].|[τ] = s.|[τ].[σ >>| τ]. Proof. autosubst. Qed.
End GeneratingOperation_SubstHSubstComp_term.

(* Table. 3 *)
(* 略 *)

(**
## Defined Operations （定義されたsubstitution操作）
*)

(* Table. 4 *)
Section DefinedOperations_1_term.
Variables (x : var) (s : term).
Variables (σ  τ : var -> term).            (* 代入 *)
Variables (Δ : term -> term).
Variable a : term.
Variable f : var -> term.

Goal (σ >>> Δ) = fun x => Δ (σ x). Proof. auto. Qed.
Locate ">>>".                               (* Lib.funcomp f g  *)

Goal a .: f = fun x => match x with O => a | S x' => f x' end. Proof. auto. Qed.
Goal σ >> τ = σ >>> (subst τ). Proof. auto. Qed.
End DefinedOperations_1_term.

Section DefinedOperations_1_type.
Variables (x : var) (s : type).
Variables (σ  τ : var -> type).            (* 代入 *)
Variables (Δ : type -> type).
Variable a : term.
Variable f : var -> term.

Goal (σ >>> Δ) = fun x => Δ (σ x). Proof. auto. Qed.
Locate ">>>".                               (* Lib.funcomp f g  *)

Goal a .: f = fun x => match x with O => a | S x' => f x' end. Proof. auto. Qed.
Goal σ >> τ = σ >>> (subst τ). Proof. auto. Qed.
End DefinedOperations_1_type.

Section DefinedOperations_2_term.
Variables (x : var) (s : term).
Variables (σ : var -> term).            (* 代入 *)
Variables (Θ : var -> term).            (* 代入 *)
Variables (ξ : var -> var).
Definition ids := fun x : var => Var x.

(* Goal σ >>| Θ = σ >>> (hsubst Θ). Proof. auto. Qed. *)
Goal ren ξ = ξ >>> ids. Proof. auto. Qed.
Goal forall n : nat, (+ n) = lift n. auto. Qed.
Print lift.                                 (* fun x : nat => [eta plus x] *)
End DefinedOperations_2_term.

Section DefinedOperations_2_type.
Variables (x : var) (s : type).
Variables (σ : var -> term).            (* 代入 *)
Variables (Θ : var -> type).            (* 代入 *)
Variables (ξ : var -> var).
Definition ids' := fun x : var => Var x.

Goal σ >>| Θ = σ >>> (hsubst Θ). Proof. auto. Qed.
Goal ren ξ = ξ >>> ids'. Proof. auto. Qed.
Goal forall n : nat, (+ n) = lift n. auto. Qed.
Print lift.                                 (* fun x : nat => [eta plus x] *)
End DefinedOperations_2_type.

(**
## The Automation Tactics
*)
(**
- asimpl : Normalizes the claim.

- autosumbst : Normalizes the claim and tries to solve the resulting equation.
*)

(**
# Internals
*)

(**
# Best Practices

## Adding Primitives to autosubst
*)

(**
# FAQ
*)

(**
- simplは、autosubsetの実装の詳細までカバーしないので、asimplを使うこと。

- constructorやapplyを使うまえに、もうこれ以上reductionしなくてよいか確認するために、
  asimplを試して(try)みること。
*)

(**
# （補足）代入をリストに拡張する。
*)

(* END *)
