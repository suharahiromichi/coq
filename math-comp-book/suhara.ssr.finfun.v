From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset Printing Implicit. (* Unset : implicitな引数を表示しない。 D:しない。 A:する。*)
Unset Printing Coercions. (* Unset : コアーションを表示しない     D:しない。 A:する。*)
Set   Printing Notations. (*   Set : Notation を使って表示する。  D:する。  A:しない。*) 
Unset Printing Universe.  (* Unset : 高階のTypeを表示しない。     D:しない。 A:- *)
Print Graph.              (* Print Coercions. *)
Print Canonical Projections.

Section Def.
  Variables (aT : finType) (rT : Type).
  
  Inductive finfun_type : predArgType := Finfun of #|aT|.-tuple rT.
  Definition finfun_of of phant (aT -> rT) := finfun_type.
  Identity Coercion type_of_finfun : finfun_of >-> finfun_type.
  Definition fgraph f := let: Finfun t := f in t.
  Canonical finfun_subType := Eval hnf in [newType for fgraph].
End Def.

Notation "{ 'ffun' fT }" := (finfun_of (Phant fT))
  (at level 0, format "{ 'ffun'  '[hv' fT ']' }") : type_scope.

(*****************************************************************************)

Local Notation fun_of_fin_def :=
  (fun aT rT f x => tnth (@fgraph aT rT f) (enum_rank x)).
Local Notation finfun_def := (fun aT rT f => @Finfun aT rT (codom_tuple f)).
Parameter fun_of_fin : forall aT rT, finfun_type aT rT -> aT -> rT.
Parameter finfun : forall (aT : finType) rT, (aT -> rT) -> {ffun aT -> rT}.

Notation "[ 'ffun' x : aT => F ]" := (finfun (fun x : aT => F))
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'ffun' : aT => F ]" := (finfun (fun _ : aT => F))
  (at level 0, only parsing) : fun_scope.

Notation "[ 'ffun' x => F ]" := [ffun x : _ => F]
  (at level 0, x ident, format "[ 'ffun'  x  =>  F ]") : fun_scope.

Notation "[ 'ffun' => F ]" := [ffun : _ => F]
  (at level 0, format "[ 'ffun' =>  F ]") : fun_scope.

Check [ffun i :'I_4 => i + 2] :{ffun 'I_4 -> nat}.

(*****************************************************************************)

Section PlainTheory.
  Variables (aT : finType) (rT : Type).
  Notation fT := {ffun aT -> rT}.
  Implicit Types (f : fT) (R : pred rT).
  
  Canonical finfun_of_subType := Eval hnf in [subType of fT].
End PlainTheory.

(*****************************************************************************)

Section EqTheory.
  Variables (aT : finType) (rT : eqType).
  Notation fT := {ffun aT -> rT}.
  Implicit Types (y : rT) (D : pred aT) (R : pred rT) (f : fT).

  Definition finfun_eqMixin :=
    Eval hnf in [eqMixin of finfun_type aT rT by <:].
  Canonical finfun_eqType := Eval hnf in EqType _ finfun_eqMixin.
(*
  Canonical finfun_of_eqType := Eval hnf in [eqType of fT].
*)
End EqTheory.

Definition finfun_choiceMixin aT (rT : choiceType) :=
  [choiceMixin of finfun_type aT rT by <:].
Canonical finfun_choiceType aT rT :=
  Eval hnf in ChoiceType _ (finfun_choiceMixin aT rT).
(*
Canonical finfun_of_choiceType (aT : finType) (rT : choiceType) :=
  Eval hnf in [choiceType of {ffun aT -> rT}].
*)

Definition finfun_countMixin aT (rT : countType) :=
  [countMixin of finfun_type aT rT by <:].
Canonical finfun_countType aT (rT : countType) :=
  Eval hnf in CountType _ (finfun_countMixin aT rT).
(*
Canonical finfun_of_countType (aT : finType) (rT : countType) :=
  Eval hnf in [countType of {ffun aT -> rT}].
*)
Canonical finfun_subCountType aT (rT : countType) :=
  Eval hnf in [subCountType of finfun_type aT rT].
(*
Canonical finfun_of_subCountType (aT : finType) (rT : countType) :=
  Eval hnf in [subCountType of {ffun aT -> rT}].
*)
(*****************************************************************************)

Section FinTheory.
  Variables aT rT : finType.
  Notation fT := {ffun aT -> rT}.
  Notation ffT := (finfun_type aT rT).
  Implicit Types (D : pred aT) (R : pred rT) (F : aT -> pred rT).
  
  Definition finfun_finMixin := [finMixin of ffT by <:]. (* finfun_subCountType が要る。 *)
  Canonical finfun_finType := Eval hnf in FinType ffT finfun_finMixin.
  Canonical finfun_subFinType := Eval hnf in [subFinType of ffT].
  Canonical finfun_of_finType := Eval hnf in [finType of fT for finfun_finType].
  Canonical finfun_of_subFinType := Eval hnf in [subFinType of fT].
End FinTheory.

(*****************************************************************************)

(* 例 *)
Check #|{ffun pred bool}| : nat.

Locate "#| _ |".                       (* "#| A |" := card (mem A)  *)
Check @card : forall (T : Finite.type) (_ : mem_pred T), nat.
Check @mem  : forall (T : Type) (pT : predType T) (_ : pT), mem_pred T.

Check {ffun pred bool} : Type.
(* finfun_type の型を predArgType にすると、以下が通るようになる。 *)
Check @finfun_of bool_finType bool  (Phant (pred bool)) : predArgType.
Check @mem _ _ (@finfun_of _ _ (Phant (pred bool))).
Check @mem _ _ {ffun pred bool}.
Check mem {ffun pred bool} : mem_pred (@finfun_of bool_finType bool (Phant (pred bool))).

Check (finfun_of_finType bool_finType bool_finType) : finType.
Check @card (finfun_of_finType bool_finType bool_finType)
      (@mem (@finfun_of bool_finType bool (Phant (pred bool)))
            (predPredType (@finfun_of bool_finType bool (Phant (pred bool))))
            (@finfun_of bool_finType bool (Phant (pred bool))))
  : nat.
Check card (mem {ffun pred bool}) : nat.

(* END *)
