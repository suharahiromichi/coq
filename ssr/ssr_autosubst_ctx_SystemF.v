(**
System F
 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import AutosubstSsr Context.

(** **** Syntax *)

Inductive type : Type :=
| TyVar (x : var)
| Arr (A1 A2 : type)
| All (A2 : {bind type}).

Inductive term :=
| TeVar (x : var)
| Abs (A : type) (s : {bind term})
| App (s t : term)
| TAbs (s : {bind type in term})
| TApp (s : term) (A : type).

(** **** Substitutions *)

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_type : SubstLemmas type. derive. Qed.
Instance HSubst_term : HSubst type term. derive. Defined.
Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed.
Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(** **** Subtyping *)

Notation "Gamma `_ x" := (dget Gamma x).
Notation "Gamma ``_ x" := (get Gamma x) (at level 3, x at level 2,
  left associativity, format "Gamma ``_ x").

(** **** Typing *)

Reserved Notation "'TY' Gamma |- A : B"
  (at level 68, A at level 99, no associativity,
   format "'TY'  Gamma  |-  A  :  B").
Inductive ty (Gamma : list type) : term -> type -> Prop :=
| ty_var x :
    x < size Gamma ->
    TY Gamma |- TeVar x : Gamma``_x
| ty_abs A B s :
    TY A::Gamma |- s : B ->
    TY Gamma |- Abs A s : Arr A B
| ty_app A B s t:
    TY Gamma |- s : Arr A B ->
    TY Gamma |- t : A ->
    TY Gamma |- App s t : B
| ty_tabs A s :
    TY Gamma..[ren (+1)] |- s : A ->
    TY Gamma |- TAbs s : All A
| ty_tapp A B s :
    TY Gamma |- s : All A ->
    TY Gamma |- TApp s B : A.[B/]
where "'TY' Gamma |- s : A" := (ty Gamma s A).

Definition value (s : term) : bool :=
  match s with Abs _ _ | TAbs _ => true | _ => false end.

Reserved Notation "'EV' s => t"
  (at level 68, s at level 80, no associativity, format "'EV'   s  =>  t").
Inductive eval : term -> term -> Prop :=
| E_AppAbs A s t : EV App (Abs A s) t => s.[t/]
| E_TAppTAbs s B : EV TApp (TAbs s) B => s.|[B/]
| E_AppFun s s' t :
     EV s => s' ->
     EV App s t => App s' t
| E_AppArg s s' v:
     EV s => s' -> value v ->
     EV App v s => App v s'
| E_TypeFun s s' A :
     EV s => s' ->
     EV TApp s A => TApp s' A
where "'EV' s => t" := (eval s t).

(** **** Preservation *)

Lemma ty_ren Gamma1 Gamma2 s A xi :
  (forall x, x < size Gamma1 -> xi x < size Gamma2) ->
  (forall x, x < size Gamma1 -> Gamma2``_(xi x) = Gamma1``_x) ->
  TY Gamma1 |- s : A -> TY Gamma2 |- s.[ren xi] : A.
Proof with eauto using ty.
  move=> h1 h2 ty. elim: ty Gamma2 xi h1 h2 => {Gamma1 s A} /=...
  - move=> Gamma1 x lt Gamma2 xi h1 h2. rewrite -h2 //. apply: ty_var...
  - move=> Gamma1 A B s _ ih Gamma2 xi h1 h2. asimpl. apply: ty_abs.
    by apply: ih => [[|x/h1]|[|x/h2]].
 - move=> Gamma1 A B s ih Gamma2 xi h1 h2. apply: ty_tabs.
    apply: ih => x. by rewrite !size_map => /h1. rewrite !size_map => lt.
    rewrite !get_map ?h2 //. exact: h1.
Qed.

Lemma ty_evar Gamma x A :
  A = Gamma``_x -> x < size Gamma -> TY Gamma |- TeVar x : A.
Proof. move->. exact: ty_var. Qed.

Lemma ty_etapp Gamma A C D s :
  D = A.[C/] ->
  TY Gamma |- s : All A ->
  TY Gamma |- TApp s C : D.
Proof. move->. exact: ty_tapp. Qed.


Lemma ty_weak Gamma s A B :
  TY Gamma |- s : A -> TY B::Gamma |- s.[ren (+1)] : A.
Proof. exact: ty_ren. Qed.

Lemma ty_hsubst Gamma s A sigma :
(*  (forall x, x < size Delta1) -> *)
  TY Gamma |- s : A -> TY Gamma..[sigma] |- s.|[sigma] :A.[sigma].
Proof with eauto using ty.
  admit.
(*
  move=> h ty. elim: ty Delta2 sigma h => {Delta1 Gamma s A}/=...
  - move=> Delta1 Gamma x lt Delta2 sigma h. apply: ty_evar. by rewrite get_map.
    by rewrite size_map.
  - move=> Delta1 Gamma A B s _ ih Delta2 sigma h. apply: ty_tabs.
    specialize (ih (A.[sigma] :: Delta2) (up sigma)). move: ih. asimpl.
    apply. move=> [_|x/h/sub_weak] /=. apply: sub_var_trans => //. autosubst.
    autosubst.
  - move=> Delta1 Gamma A B C s _ ih sub Delta2 sigma h. asimpl.
    eapply ty_etapp. Focus 2. by eapply ih. autosubst. exact: sub_subst sub.
  - move=> Delta1 Gamma A B s _ ih sub Delta2 sigma h.
    eapply ty_sub. by eapply ih. exact: sub_subst sub.
*)
Qed.

Lemma ty_tweak Gamma s A :
  TY Gamma |- s : A ->
  TY Gamma..[ren (+1)] |- s.|[ren (+1)] : A.[ren (+1)].
Proof.
  apply: ty_hsubst => x. (* exact: sub_var_trans. *)
Qed.

Lemma ty_subst Gamma1 Gamma2 s A sigma :
  (forall x, x < size Gamma1 -> TY Gamma2 |- sigma x : Gamma1``_x) ->
  TY Gamma1 |- s : A -> TY Gamma2 |- s.[sigma] : A.
Proof with eauto using ty.
  move=> h ty. elim: ty Gamma2 sigma h => {Gamma1 s A}/=...
  - move=> Gamma1 A B s _ ih Gamma2 sigma h /=. apply: ty_abs.
    move: ih. apply; move=> [/= | x /h /ty_weak].
    + intros. apply ty_var. auto.
    + autosubst.
  - move=> Gamma1 A B s ih Gamma2 sigma h. apply: ty_tabs. apply: ih.
    move=> x. rewrite size_map => lt. rewrite get_map //=. exact/ty_tweak/h.
Qed.

(* ***** *)

Lemma ty_beta Gamma s t A B :
  TY Gamma |- t : A -> TY A::Gamma |- s : B ->
  TY Gamma |- s.[t/] : B.
Proof.
  move=> ty. apply: ty_subst => -[|n lt] //=. exact: ty_var.
Qed.

Lemma ty_inv_abs' Gamma A A' B T s :
  TY Gamma |- Abs A s : T ->
  TY A'::Gamma |- s : B.
Proof.
  move: (Abs A s) => t ty. elim: ty A s => {Gamma t} //.
 - move=> Gamma x h B' s'.
 admit.                                     (* XXXXX *)
  eauto using ty.
 admit.                                     (* XXXXX *)
  eauto using ty.

 admit.                                     (* XXXXX *)
Qed.

Lemma ty_inv_abs Gamma A A' B s :
  TY Gamma |- Abs A s : Arr A' B -> TY A'::Gamma |- s : B.
Proof.
  move=> ty. apply: ty_inv_abs' ty.
Qed.


(* ***** *)


Lemma ty_betaT Gamma s A B :
  TY Gamma..[ren (+1)] |- s : A ->
  TY Gamma |- s.|[B/] : A.[B/].
Proof.
  move=> ty.
  Check ty_hsubst.
  admit.                                    (* XXXX *)
Qed.

Lemma ty_inv_tabs' Gamma B T s :
  TY Gamma |- TAbs s : T ->
  TY Gamma..[ren(+1)] |- s : B.
Proof.
  move e: (TAbs s) => t ty.
  elim: ty B s e => {Gamma t T} //.
  move=> Gamma s ty ih H0 A' s' e.
  admit.                                    (* XXXX *)
Qed.

Lemma ty_inv_tabs Gamma B s :
  TY Gamma |- TAbs s : All B ->
  TY Gamma..[ren(+1)] |- s : B.
Proof.
  move=> ty.
  apply: (ty_inv_tabs' _ _ (All B)).
  by [].
Qed.

(* ***** *)

Theorem preservation Gamma s t A :
  TY Gamma |- s : A -> EV s => t -> TY Gamma |- t : A.
Proof with eauto using ty.
  move=> ty. elim: ty t => {Gamma s A}...
  - move=> Gamma x _ t ev. by inv ev.
  - move=> Gamma A B s _ i t ev. by inv ev.
  - move=> Gamma A B s t ty1 ih1 ty2 ih2 u ev.
    inversion ev.               (* inv ev *)
    (* ty1 :  TY Gamma |- Abs A0 s0 : Arr A B これがおかしい？
  そのため、ty_inv_abs がおかしい（証明不能）なものを使っている。
  ty1 がおかしくなるのは、EV App ... の一番最初の条件のinv.
  inversion あとの subst.  で、H0 : Abs A0 s0 = s が代入される。
     *)
    subst.
    Check ty_inv_abs.
    (* move: ty1. move/ty_inv_abs. exact: ty_beta. *)
    apply ty_inv_abs in ty1. move: ty1. exact: ty_beta.
    eauto using ty.
    eauto using ty.
  - move=> Gamma A B s _ t ev. by inv ev.
  - move=> Gamma A B s ty ih t ev. inv ev.
    + move: ty0 => /ty_inv_tabs H. apply: (ty_betaT _ s0 _ _)...
    + apply: ty_tapp...
Qed.

(** **** Progress *)

Definition is_abs s := if s is Abs _ _ then true else false.
Definition is_tabs s := if s is TAbs _ then true else false.

Lemma canonical_arr Gamma s A B :
  TY Gamma |- s : Arr A B -> value s -> is_abs s.
Proof.
  admit.
Qed.

Lemma canonical_all Gamma s A :
  TY Gamma |- s : All A -> value s -> is_tabs s.
Proof.
  admit.
Qed.

Lemma ev_progress' Gamma s A :
  TY Gamma |- s : A -> Gamma = [::] -> value s \/ exists t, EV s => t.
Proof with eauto using eval.
  elim=> {Gamma s A} /=; try solve [intuition].
  - move=> Gamma x lt eqn. by subst.
  - move=> Gamma A B s t ty1 ih1 _ ih2 eqn. right.
    case: (ih1 eqn) => {ih1} [vs|[s' h1]]...
    case: (ih2 eqn) => {ih2 eqn} [vt|[t' h2]]...
    case: s {ty1 vs} (canonical_arr _ _ _ _ ty1 vs) => //...
  - move=> Gamma A B s ty ih eqn. right.
    case: (ih eqn) => {ih eqn}[vs|[s' h]]...
    case: s {ty vs} (canonical_all _ _ _ ty vs) => //.
    move=> s H.
    exists s.|[B/].
    apply E_TAppTAbs.
Qed.

Theorem ev_progress s A:
  TY nil |- s : A -> value s \/ exists t,  EV s => t.
Proof. move=> ty. exact: ev_progress' ty _. Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Ssr")) *)
(* End: *)
