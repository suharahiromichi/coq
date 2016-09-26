From mathcomp Require Import all_ssreflect.

(* 6. Sub-Types Terms with properties *)
(* 6.5 Finite functions *)

Section FinFunDef.
  Variables (aT : finType) (rT : Type).
  
  Inductive finfun : Type := Finfun of #|aT|.-tuple rT.
  
  Definition fgraph f := let: Finfun t := f in t.
  
  Canonical finfun_subType := Eval hnf in [newType for fgraph].
  Eval hnf in [newType for fgraph].         (* [subType for fgraph] *)
  
End FinFunDef.

Notation "{ ’ffun’ fT }" := (finfun fT).

Definition fun_of_fin aT rT f x := tnth (@fgraph aT rT f) (enum_rank x).
(* Coercion fun_of_fin : finfun >-> FunClass. *)
(* Definition finfun aT rT f := @Finfun aT rT (codom_tuple f). *)

Notation "[’ffun’x : aT => F ]" := (finfun (fun x : aT => F)).

Check [ffun i : 'I_4 => i + 2] : {ffun ordinal_finType 4 -> nat}.

(* eqType の継承 *)
Definition finfun_eqMixin aT (rT : eqType) :=
  Eval hnf in [eqMixin of finfun aT rT by <:].
Canonical finfun_eqType aT (rT : eqType) :=
  Eval hnf in EqType (finfun aT rT) (finfun_eqMixin aT rT).

(* codomain も有限な場合 *)

(* Exercise 7 の答え *)
Definition all_words n T (alphabet : seq T) :=
  let prepend x wl := [seq x :: w | w <- wl] in
  let extend wl := flatten [seq prepend x wl | x <- alphabet] in
  iter n extend [:: [::] ].

(*
Definition tuple_enum (T : finType) n : seq (n.-tuple T) :=
  pmap insub (all_words n (enum T)).

Lemma enumP T n : Finite.axiom (tuple_enum T n).
*)

(* finfun としての tuple *)
Definition tuple_finMixin (n : nat_eqType) (T : finType) :=
  Eval hnf in FinMixin (@FinTuple.enumP n T).
Canonical tuple_finType (n : nat_eqType) (T : finType) :=
  Eval hnf in FinType (n.-tuple T) (tuple_finMixin n T).

Definition finfun_finMixin (aT rT : finType)  :=
  [finMixin of (finfun_type aT rT) by <:].
Canonical finfun_finType (aT rT : finType)  :=
  Eval hnf in FinType (finfun_type aT rT) (finfun_finMixin aT rT).

Lemma card_ffun (aT rT : finType) : #|{ffun aT -> rT}| = #|rT| ^ #|aT|.
Proof.
Admitted.

Definition eqfun (A B : Type) (f g : B -> A) : Prop :=
  forall x, f x = g x.
Notation "f1 =1 f2" := (eqfun f1 f2).

(*
Lemma ffunP (aT rT : Type) (f1 f2 : {ffun aT -> rT}) : f1 =1 f2 <-> f1 = f2.
Proof.
  Admitted.
 *)

(*
Lemma bigA_distr_bigA (I J : finType) F :
  \big[*%M/1]_(i : I) \big[+%M/0]_(j : J) F i j
    = \big[+%M/0]_(f : {ffun I -> J}) \big[*%M/1]_i F i (f i).
 *)

(* END *)
