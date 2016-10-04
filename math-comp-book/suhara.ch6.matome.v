From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm.

(* Mathcomp の数学体系 --- 有限型まで *)

(* ***************** *)
(* 1. Bool, Nat, Seq *)
(* ***************** *)
Definition bool_eqMixin' := @EqMixin bool eqb eqbP.
Canonical  bool_eqType'  := EqType bool bool_eqMixin'.

Definition nat_eqMixin'  := @EqMixin nat eqn (@eqnP).
Canonical  nat_eqType'   := EqType nat nat_eqMixin'.

Definition seq_eqMixin' (T : eqType) := @EqMixin (seq T) (@eqseq T) (@eqseqP T).
Canonical  seq_eqType'  (T : eqType) := EqType (seq T) (seq_eqMixin' T).

Definition prod_eqMixin' (T1 T2 : eqType) :=
  @EqMixin (T1 * T2) (pair_eq T1 T2) (@pair_eqP T1 T2).
Canonical  prod_eqType'  (T1 T2 : eqType) :=
  EqType (T1 * T2) (prod_eqMixin' T1 T2).

(* ************** *)
(* subtype kit *)
(* ************** *)
(*
Section MySubTypeKit.
  Variables (T : Type) (P : pred T).
  
  Structure subType' : Type :=
    SubType' {
        sub_sort :> Type;                   (* projector *)
        val : sub_sort -> T;                (* constructor *)
        Sub : forall x, P x -> sub_sort;    (* constructor *)
        (* elimination rule for sub_sort *)
        _: forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
        _: forall x Px, val (@Sub x Px) = x
      }.
  
  Notation "[ 'subType' 'for' v ]" :=
    (SubType' _ v _
              (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px)
              (fun x px => erefl x))
      (at level 0, only parsing) : form_scope.
End MySubTypeKit.
 *)

(* ********** *)
(* 2. ordinal *)
(* ********** *)
Definition ordinal_eqMixin' (n : nat) := [eqMixin of (ordinal n) by <:].
(* (@val_eqP nat_eqType (fun x : nat => x < n) (ordinal_subType n)) *)
Canonical  ordinal_eqType'  (n : nat) := EqType (ordinal n) (ordinal_eqMixin' n).

(* 重複がないこと、漏れがないこと、から定義する。 *)
Definition ordinal_finMixin' (n : nat) :=
  @UniqFinMixin _ (ord_enum n) (ord_enum_uniq n) (@mem_ord_enum n).
Canonical  ordinal_finType'  (n : nat) :=
  FinType (ordinal n) (ordinal_finMixin' n).

(* ******** *)
(* 3. Tuple *)
(* ******** *)
Structure tuple_of' (n : nat) (T : Type) :=
  Tuple' {
      tval' :> seq T;
      _     : size tval' == n
    }.
Notation "n .-TUPLE" := (tuple_of' n)
                          (at level 2, format "n .-TUPLE") : type_scope.
Check tval' : forall (n : nat) (T : Type), n.-TUPLE T -> seq T.

Canonical  tuple_subType' (n : nat) (T : Type) := [subType for tval' n T].

Definition tuple_eqMixin' (n : nat) (T : finType) := [eqMixin of n.-TUPLE T by <:].
(* (@val_eqP (seq_eqType T) (fun x : seq T => size x == n) (tuple_subType n T)) *)
Canonical  tuple_eqType'  (n : nat) (T : finType) :=
  EqType (n.-TUPLE T) (tuple_eqMixin' n T).

(* countType と enum (seq) から定義する。 *)
Definition tuple_finMixin' (n : nat) (T : finType) :=
  @FinMixin (tuple_countType n T) (FinTuple.enum n T) (@FinTuple.enumP n T).
Canonical  tuple_finType' (n : nat) (T : finType) :=
  FinType (tuple_countType n T) (tuple_finMixin' n T).

(* ********* *)
(* 4. FinFun *)
(* ********* *)
Inductive finfun' (aT : finType) (rT : Type) : Type :=
  Finfun' of #|aT|.-TUPLE rT.
Notation "{ 'FFUN' fT }" := (finfun' fT).
Definition fgraph' (aT : finType) (rT : Type) (f : {FFUN aT} rT) :=
  let: Finfun' t := f in t.
(* match f with | Finfun' t => t end. *)

Check fgraph' : forall (aT : finType) (rT : Type), { FFUN aT} rT -> #|aT|.-TUPLE rT.
Canonical  finfun_subType' (aT : finType) (rT : Type) := [newType for fgraph' aT rT].

Definition finfun_eqMixin' (aT rT : finType) := [eqMixin of {FFUN aT} rT by <:].
(* (@val_eqP (tuple_eqType #|aT| rT) xpredT (finfun_subType aT rT)) *)
Canonical  finfun_eqType'  (aT rT : finType) := EqType ({FFUN aT} rT) (finfun_eqMixin' aT rT).

Definition finfun_finMixin' (aT rT : finType) := [finMixin of finfun_type aT rT by <:].
Canonical  finfun_finType'  (aT rT : finType) :=
  FinType (finfun_type aT rT) (finfun_finMixin' aT rT).

(* ********* *)
(* 5. FinSet *)
(* ********* *)
(*
Inductive set_type' (T : finType) : predArgType :=
  FinSet' of {FFUN pred T}.
Notation "{ 'SET' T }" := (set_type' T).
Definition finfun_of_set' (T : finType) (A : {SET T}) :=
  let: FinSet' f := A in f.
(* match A with | FinSet' t => t end. *)
Check finfun_of_set' : forall T : finType, { SET T} -> { FFUN T} (pred T).
Check finfun_of_set' : forall T : finType, { SET T} -> finfun' T (pred T).

Canonical  set_subType' (T : finType) (A : set_type' T) := [newType for finfun_of_set' T A].

Definition set_eqMixin'    (T : finType) := [eqMixin of {SET T} by <:].
(* (@val_eqP (finfun_of_eqType T bool_eqType) xpredT (set_subType T)) *)
Canonical  set_eqType'     (T : finType) := EqType {SET T} (set_eqMixin' T).

Definition set_finMixin'    (T     : finType) := [finMixin of {set T} by <:].
Canonical  set_finType'     (T     : finType) :=
  FinType {set T} (set_finMixin' T).
*)

(* ******* *)
(* 6. Perm *)
(* ******* *)
Inductive perm_of' (T : finType) : Type :=
  Perm' (pval' : finfun' (T -> T)) & injectiveb pval'.
(* Notation "{ ’perm’ T }" := (perm_of' T). *)
Definition pval' (T : finType) (p : perm_of' T) :=
  let : Perm' f _ := p in f.

Canonical perm_subType' (T : finType) := [subType for pval' T].

Definition perm_finMixin'   (T     : finType) := [finMixin of perm_of' T by <:].
Canonical  perm_finType'    (T     : finType) :=
  FinType {perm T} (perm_finMixin' T).

Definition perm_eqMixin'   (T : finType) := [eqMixin of (perm_of' T) by <:].
(* (@val_eqP (finfun_of_eqType T T)
      (fun x : {ffun T -> T} => injectiveb (aT:=T) (rT:=T) x) 
      (perm_subType T)) *)
Canonical  perm_eqType'    (T : finType) := EqType (perm_of' T) (perm_eqMixin' T).

(* Q.E.D. *)
