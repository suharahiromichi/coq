From mathcomp Require Import all_ssreflect.

(* 6. Sub-Types Terms with properties *)
(* 6.5 Finite functions *)

Section FinFunDef.
  Variables (aT : finType) (rT : Type).
  
  Inductive finfun_type : Type := Finfun of #|aT|.-tuple rT.
  (* テキストは finfun だが、finfun_type に変更する。 *)
  
  Definition fgraph f := let: Finfun t := f in t.
  (* Finfun 構造体から tupple を取り出す。 *)
  
  Canonical finfun_subType := Eval hnf in [newType for fgraph].
  Eval hnf in [newType for fgraph].         (* [subType for fgraph] *)
End FinFunDef.

(* Notation "{ 'ffun' aT -> rT }" := (finfun_type aT rT). *)
(* Notation "{ 'ffun' fT }" := (finfun_type (Phant fT)). *)

(* 有限ドメイン関数から通常の関数に変換する。 *)
Check fgraph : forall (aT : finType) (rT : Type), (finfun_type aT rT) -> #|aT|.-tuple rT.
Check @enum_rank : forall T : finType, T -> 'I_ _.
Check tnth : forall (n : nat) (T : Type), n.-tuple T -> 'I_n -> T.

Definition fun_of_fin (aT : finType) (rT : Type) (f : finfun_type aT rT) : (aT -> rT) :=
  fun (x : aT) => tnth (@fgraph aT rT f) (enum_rank x).
Coercion fun_of_fin : finfun_type >-> Funclass.

(* 通常の関数から有限ドメイン関数に変換する。 *)
Check codom_tuple : forall (aT : finType) (rT : Type), (aT -> rT) -> #|aT|.-tuple rT.

Definition finfun (aT : finType) (rT : Type) (f : aT -> rT) : (finfun_type aT rT) :=
  @Finfun aT rT (codom_tuple f).

Notation "[ 'ffun' x : aT => F ]" := (finfun _ _ (fun x : aT => F)).

Check [ffun i : 'I_4 => i + 2] : finfun_type (ordinal_finType 4) nat.
Check {ffun ordinal_finType 4 -> nat}.

(* eqType の継承 *)
Definition finfun_eqMixin (aT : finType) (rT : eqType) :=
  Eval hnf in [eqMixin of finfun_type aT rT by <:].
Canonical finfun_eqType (aT : finType) (rT : eqType) :=
  Eval hnf in EqType (finfun_type aT rT) (finfun_eqMixin aT rT).

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

(* 有限型としての としての 有限tuple (有限型を要素とするtuple) *)
Definition tuple_finMixin (n : nat_eqType) (T : finType) :=
  Eval hnf in FinMixin (@FinTuple.enumP n T).
Canonical tuple_finType (n : nat_eqType) (T : finType) :=
  Eval hnf in FinType (n.-tuple T) (tuple_finMixin n T).

(* 有限型としてのfinfun *)
Unset Printing Implicit.    (* Unset : implicitな引数を表示しない。 D:しない。 A:する。*)
Unset Printing Coercions.   (* Unset : コアーションを表示しない     D:しない。 A:する。*)
Unset Printing Notations. (*   Set : Notation を使って表示する。  D:する。  A:しない。*) 
Unset Printing Universe.  (* Unset : 高階のTypeを表示しない。     D:しない。 A:- *)

(* 上で定義した funfun_type ではうまくいかない。 *)
Definition finfun_finMixin (aT rT : finType)  :=
  [finMixin of (finfun.finfun_type aT rT) by <:].
Canonical finfun_finType (aT rT : finType)  :=
  Eval hnf in FinType (finfun.finfun_type aT rT) (finfun_finMixin aT rT).

(* [finMixin of T] の T は、a subCountType structure over a type
   that has a finType structure. *)
(* [finMixin of T by <:] == a finType structure for T, when T has a subType   *)
(*                   structure over an existing finType.                      *)

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
