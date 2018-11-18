Require Import Maps.
Require Import Smallstep.

Module STLC.

(* ================================================================= *)
(** ** Types *)

Inductive ty : Type :=
  | TBool  : ty
  | TArrow : ty -> ty -> ty.

(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

(** Some examples... *)

Definition x := (Id "x").
Definition y := (Id "y").
Definition z := (Id "z").

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(** [idB = \x:Bool. x] *)

Notation idB :=
  (tabs x TBool (tvar x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB :=
  (tabs x (TArrow TBool TBool) (tvar x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
  (tabs x (TArrow (TArrow TBool TBool)
                      (TArrow TBool TBool))
    (tvar x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (tabs x TBool (tabs y TBool (tvar x))).

(** [notB = \x:Bool. if x then false else true] *)

Notation notB := (tabs x TBool (tif (tvar x) tfalse ttrue)).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true :
      value ttrue
  | v_false :
      value tfalse.

(* Hint Constructors value. *)

(** ** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if beq_id x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if beq_id x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue =>
      ttrue
  | tfalse =>
      tfalse
  | tif t1 t2 t3 =>
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Reserved Notation "t1 '==>' t2" (at level 40).

Module CBV.
(*
http://xenophobia.hatenablog.com/entry/2013/12/02/225511
(define $beta-reduce-cbv-naive
  (match-lambda term
    {
     [<app <lam $x $t> (value $v)>        ((subst x v) t)] ;;;;;
     [<app $t1 $t2>                       <App (beta-reduce-cbv-naive t1) t2>]
     [<app (value $v) $t>                 <App v (beta-reduce-cbv-naive t)>] ;;;;;
     [<op $ope (value $v1) (value $v2)>   ((op-reduce ope) v1 v2)]
     [<op $ope (value $v) $t>             <Op ope v (beta-reduce-cbv-naive t)>]
     [<op $ope $t1 $t2>                   <Op ope (beta-reduce-cbv-naive t1) t2>]
     [$v v]
}))
  *)

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

End CBV.

Module CBN.
(*
http://xenophobia.hatenablog.com/entry/2013/12/02/225511
(define $beta-reduce-cbn-naive
  (match-lambda term
    {[<app <lam $x $t1> $t2>              ((subst x t2) t1)]
     [<app $t1 $t2>                       <App (beta-reduce-cbn-naive t1) t2>]
     [<op $ope (value $v1) (value $v2)>   ((op-reduce ope) v1 v2)]
     [<op $ope (value $v) $t>             <Op ope v (beta-reduce-cbn-naive t)>]
     [<op $ope $t1 $t2>                   <Op ope (beta-reduce-cbn-naive t1) t2>]
      [$v v]}))
  *)

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
      (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tapp t1 t2 ==> tapp t1' t2
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

End CBN.

(* ******** *)
(* Examples *)
(* ******** *)

(** Example:

      (\x:Bool->Bool. x) (\x:Bool. x) ==>* \x:Bool. x

    i.e.,

      idBB idB ==>* idB
*)

Import CBV.
Lemma step_cbv_exapmle1' :
  (tapp idBB idB) ==> idB.
Proof.
  apply ST_AppAbs.
  now apply v_abs.
Qed.

Lemma step_cbv_exapmle1 :
  (tapp idBB idB) ==>* idB.
Proof.
  Check (multi_step step (tapp idBB idB) idB idB).
  apply (multi_step step (tapp idBB idB) idB idB).
  Undo 1.
  apply multi_step with (y:=idB).
  Undo 1.
  eapply multi_step.
  - apply ST_AppAbs.
    now apply v_abs.
  - now apply multi_refl.
Qed.

Import CBN.
Lemma step_cbn_exapmle1' :
  (tapp idBB idB) ==> idB.
Proof.
  now apply ST_AppAbs.
Qed.

Lemma step_cbn_exapmle1 :
  (tapp idBB idB) ==>* idB.
Proof.
  Check (multi_step step (tapp idBB idB) idB idB).
  apply (multi_step step (tapp idBB idB) idB idB).
  Undo 1.
  apply multi_step with (y:=idB).
  Undo 1.
  eapply multi_step.
  - now apply ST_AppAbs.
  - now apply multi_refl.
Qed.

(** Example:

      (\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))
            ==>* \x:Bool. x

    i.e.,

      (idBB (idBB idB)) ==>* idB.
*)

Import CBV.
Lemma step_cbv_exapmle2 :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  eapply multi_step.
  - apply ST_App2.
    + now apply v_abs.
    + apply ST_AppAbs.
      now apply v_abs.
  - eapply multi_step.
    * apply ST_AppAbs.
      now apply v_abs.
    * now apply multi_refl.
Qed.

Import CBN.
Lemma step_cbn_exapmle2 :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  eapply multi_step.
  - now apply ST_AppAbs.
  - eapply multi_step.
    + now apply ST_AppAbs.
    + now apply multi_refl.
Qed. 

(** Example:

      (\x:Bool->Bool. x) 
         (\x:Bool. if x then false else true) 
         true
            ==>* false

    i.e.,

       (idBB notB) ttrue ==>* tfalse.
*)

Import CBV.
Lemma step_cbv_exapmle3 :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof.
  eapply multi_step.
  - apply ST_App1.
    apply ST_AppAbs.
    now apply v_abs.
  - eapply multi_step.
    + apply ST_AppAbs.
      now apply v_true.
    + eapply multi_step.
      * now apply ST_IfTrue.
      * now apply multi_refl.
Qed.

Import CBN.
Lemma step_cbn_exapmle3 :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof.
  eapply multi_step.
  - apply ST_App1.
    now apply ST_AppAbs.
  - eapply multi_step.
    + now apply ST_AppAbs.
    + eapply multi_step.
      * now apply ST_IfTrue.
      * now apply multi_refl.
Qed.

(** Example:

      (\x:Bool -> Bool. x) 
         ((\x:Bool. if x then false else true) true)
            ==>* false

    i.e.,

      idBB (notB ttrue) ==>* tfalse.
*)

Import CBV.
Lemma step_cbv_exapmle4 :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof.
  eapply multi_step.
  - apply ST_App2.
    + now apply v_abs.
    + apply ST_AppAbs.
      now apply v_true.
  - eapply multi_step.
    + apply ST_App2.
      * now apply v_abs.
      * now apply ST_IfTrue.
    + eapply multi_step.
      * apply ST_AppAbs.
        now apply v_false.
      * now apply multi_refl.
Qed.

Import CBN.
Lemma step_cbn_exapmle4 :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof.
  eapply multi_step.
  - now apply ST_AppAbs.
  - eapply multi_step.
    + now apply ST_AppAbs.
    + eapply multi_step.
      * now apply ST_IfTrue.
      * now apply multi_refl.
Qed.

(*
Hint Constructors value.

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

Lemma step_example1' :
  (tapp idBB idB) ==>* idB.
Proof.
  normalize.
Qed.

Lemma step_example2' :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. normalize.  Qed.

Lemma step_example4' :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. normalize.  Qed.
*)

End STLC.

(* END *)
