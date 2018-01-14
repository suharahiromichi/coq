From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. (* SSReflect *)
From Autosubst Require Import Autosubst.    (* !! Autosubst !! *)

Inductive term : Type :=
| Var (x : var)
| App (s t : term)
| Lam (s : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Section Test.

Variables (x y : var)
          (s t : term)
          (σ τ : var -> term)             (* substitution *)
          (ξ : var -> var).                (* rename *)

Check Var x : term.
Check App s t : term.
Check Lam s : term.

(* 定数 *)
Check ids : var -> term.                    (* subst *)
Check rename : (var -> var) -> term -> term.
Check subst  : (var -> term) -> term -> term.

Check (+1) : var -> var.                    (* rename *)
Check up   : (var -> term) -> var -> term.
Check ren  : (var -> var) -> var -> term.

(* Notation *)
Locate "_ .: _".                            (* scons *)
Locate "_ .[ _ ]".                          (* subst *)
Locate "_ >> _".                            (* scomp *)

Check scons : _ -> (var -> _) -> var -> _. (* substitution または rename のcons *)
Check subst : (var -> term) -> term -> term. (* substitution を term に適用する。 *)
Check scomp : (var -> term) -> (var -> term) -> var -> term. (* substitution の合成 *)
Check ren   : (var -> var) -> var -> term. (* rename から substitution をつくる。 *)

(* SubstLemmas に含まれる補題 *)
Check rename_subst : forall (ξ : var -> var) (s : term), rename ξ s = s.[ren ξ].
Check subst_id     : forall s : term, s.[ids] = s.
Check id_subst     : forall (σ : var -> term) (x : var), (ids x).[σ] = σ x.
Check subst_comp   : forall (σ τ : var -> term) (s : term), s.[σ].[τ] = s.[σ >> τ].

Goal ren ξ = ξ >>> ids.                   (* substitution *)
  reflexivity.
Qed.

Goal σ >> τ = σ >>> subst τ.            (* substitution *)
  reflexivity.
Qed.

Goal up σ = (Var 0) .: (σ >> ren (+1)).   (* substitution *)
  by autosubst.                             (* upE *)
Qed.

Goal ids x = Var x.                         (* term *)
  reflexivity.
Qed.

Goal rename ξ s = s.[ren ξ].              (* term *)
    by autosubst.                           (* rename_subst *)
Qed.

Goal s.[ids] = s.                           (* term *)
    by autosubst.                           (* subst_id. *)
Qed.

Goal (ids x).[σ] = σ x.                   (* term *)
    by autosubst.                           (* id_subst *)
Qed.

Goal s.[σ].[τ] = s.[σ >> τ].            (* term *)
    by autosubst.                           (* subst_comp *)
Qed.

Check scons : term -> (var -> term) -> var -> term.
Goal (s .: σ) 0 = s.                       (* term *)
    by [].
Qed.

Goal (s .: σ) x.+1 = σ x.                 (* term *)
    by [].
Qed.

Goal (Var x).[σ] = σ(x).                  (* term *)
    by [].
Qed.

Goal (App s t).[σ] = App s.[σ] t.[σ].    (* term *)
    by [].
Qed.

Goal (Lam s).[σ] = Lam s.[up σ].          (* term *)
    by [].
Qed.

Goal up σ 0 = Var 0.                       (* term *)
  reflexivity.
Qed.

Goal up σ x.+1 = (σ x).[ren (+1)].        (* term *)
  autosubst.
Qed.

Goal (σ >> τ) x = (σ x).[τ].            (* term *)
    by [].
Qed.

Check scons : var -> (var -> var) -> var -> var.
Goal (y .: ξ) 0 = y.                       (* var *)
    by [].
Qed.

Goal (y .: ξ) x.+1 = ξ x.                 (* var *)
    by [].
Qed.

Goal (+1) x = x.+1.                         (* var *)
    by [].
Qed.
End Test.

(** **** One-Step Reduction *)

Inductive step : term -> term -> Prop :=
| step_beta s t :                   step (App (Lam s) t) s.[t .: ids]
| step_appL s1 s2 t : step s1 s2 -> step (App s1 t) (App s2 t)
| step_appR s t1 t2 : step t1 t2 -> step (App s t1) (App s t2)
| step_lam s1 s2 :    step s1 s2 -> step (Lam s1) (Lam s2).

Lemma step_ebeta (s t u : term) : s.[t .: ids] = u -> step (App (Lam s) t) u.
Proof.
  move=> <-.
  exact: step_beta.
Qed.

Lemma step_subst σ s t : step s t -> step s.[σ] t.[σ].
Proof.
  move=> st.
  elim: st σ => /= {s t}; auto using step.
  move=> s t σ.
  apply: step_ebeta.
    by autosubst.                           (* asimpl. *)
Qed.

(* END *)
