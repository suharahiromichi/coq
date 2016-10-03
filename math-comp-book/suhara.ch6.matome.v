From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm.

(* Mathcomp の数学体系 --- 有限型まで *)

(* 1. サブタイプの定義 *)

Structure tuple_of n T :=
  Tuple {
      tval' :> seq T;
      _ : size tval' == n
    }.
Notation   "n .-tuple T"   := (tuple_of n T)
   (at level 10, format "n .-tuple T") : type_scope.

(* 2. eqType の定義 *)

Definition bool_eqMixin' := @EqMixin bool eqb eqbP.
Canonical  bool_eqType'  := EqType bool bool_eqMixin'.

Definition nat_eqMixin'  := @EqMixin nat eqn (@eqnP).
Canonical  nat_eqType'   := EqType nat nat_eqMixin'.

Definition seq_eqMixin' (T : eqType) := @EqMixin (seq T) (@eqseq T) (@eqseqP T).
Canonical  seq_eqType'  (T : eqType) := EqType (seq T) (seq_eqMixin' T).


(* サブタイプから定義する。 *)
Definition prod_eqMixin' (T1 T2 : eqType) :=
  @EqMixin (T1 * T2) (pair_eq T1 T2) (@pair_eqP T1 T2).
Canonical  prod_eqType'  (T1 T2 : eqType) :=
  EqType (T1 * T2) (prod_eqMixin' T1 T2).

Definition tuple_eqMixin' (n : nat) (T : finType) := [eqMixin of n.-tuple T by <:].
(* (@val_eqP (seq_eqType T) (fun x : seq T => size x == n) (tuple_subType n T)) *)
Canonical  tuple_eqType'  (n : nat) (T : finType) :=
  EqType (n.-tuple T) (tuple_eqMixin' n T).

Definition ordinal_eqMixin' (n : nat) := [eqMixin of (ordinal n) by <:].
(* (@val_eqP nat_eqType (fun x : nat => x < n) (ordinal_subType n)) *)
Canonical  ordinal_eqType'  (n : nat) := EqType (ordinal n) (ordinal_eqMixin' n).

Definition finfun_eqMixin' (aT rT : finType) := [eqMixin of finfun_type aT rT by <:].
(* (@val_eqP (tuple_eqType #|aT| rT) xpredT (finfun_subType aT rT)) *)
Canonical  finfun_eqType'  (aT rT : finType) := EqType _ (finfun_eqMixin' aT rT).

Definition set_eqMixin'    (T : finType) := [eqMixin of (set_type T) by <:].
(* (@val_eqP (finfun_of_eqType T bool_eqType) xpredT (set_subType T)) *)
Canonical  set_eqType'     (T : finType) := EqType (set_type T) (set_eqMixin' T).

Definition perm_eqMixin'   (T : finType) := [eqMixin of (perm_type T) by <:].
(* (@val_eqP (finfun_of_eqType T T)
     (fun x : {ffun T -> T} => injectiveb (aT:=T) (rT:=T) x) 
     (perm_subType T)) *)
Canonical  perm_eqType'    (T : finType) := EqType (perm_type T) (perm_eqMixin' T).



(* 3. 有限型の定義 *)

(* 有限型の公理 要素が1個づつ から定義する。 *)
Definition bool_finMixin' := @FinMixin _ [:: true; false] bool_enumP.
Canonical  bool_finType'  := FinType bool bool_finMixin'.

(* eqType と enum から定義する。 *)
Definition tuple_finMixin' (n : nat) (T : finType) :=
  @FinMixin (tuple_countType n T) (FinTuple.enum n T) (@FinTuple.enumP n T).
Canonical tuple_finType' (n : nat) (T : finType) :=
  FinType (n.-tuple T) (tuple_finMixin' n T).

(* 重複がないこと、漏れがないこと、から定義する。 *)
Definition ordinal_finMixin' (n : nat) :=
  @UniqFinMixin _ (ord_enum n) (ord_enum_uniq n) (@mem_ord_enum n).
Canonical  ordinal_finType'  (n : nat) :=
  FinType (ordinal n) (ordinal_finMixin' n).

(* サブタイプから定義する。 *)
Definition finfun_finMixin' (aT rT : finType) := [finMixin of finfun_type aT rT by <:].
Canonical  finfun_finType'  (aT rT : finType) :=
  FinType (finfun_type aT rT) (finfun_finMixin' aT rT).

Definition set_finMixin'    (T     : finType) := [finMixin of set_type T by <:].
Canonical  set_finType'     (T     : finType) :=
  FinType (set_type T) (set_finMixin' T).

Definition perm_finMixin'   (T     : finType) := [finMixin of perm_type T by <:].
Canonical  perm_finType'    (T     : finType) :=
  FinType (perm_type T) (perm_finMixin' T).

(* Q.E.D. *)


(* *********************************************** *)
(* *********************************************** *)
(* *********************************************** *)
(* *********************************************** *)
(* *********************************************** *)




Inductive test : Type := t1 | t2.
Fail Check [:: t1] == [:: t2].
(* "seq test" while it is expected to have type "Equality.sort ?T". *)

Variables (a : 3.-tuple test) (b : 3.-tuple test).
Fail Check a == b.

Variables (f : {ffun bool -> test}) (g : {ffun bool -> test}).
Fail Check f == g.

Variable (s : {set bool}) (t : {set bool}).
Check s == t.

Variables (p : {perm bool}) (q : {perm bool}).
Check p == q.

(* サブタイプを作るための関数 *)
Check tval : forall (n : nat) (T : Type), n.-tuple T -> seq T.
Check nat_of_ord : forall n : nat, 'I_n -> nat.
Check fgraph : forall (aT : finType) (rT : Type), finfun_type aT rT -> #|aT|.-tuple rT.
Check finfun_of_set : forall T : finType, set_type T -> {ffun pred T}.
Check pval : forall T : finType, perm_type T -> {ffun T -> T}.

(* ***** *)
Check EqMixin : forall (T : Type) (op : rel T),
    Equality.axiom (T:=T) op -> Equality.mixin_of T.
Print Equality.axiom. (* fun (T : Type) (e : rel T) => forall x y : T, reflect (x = y) (e x y) *)
Check @pair_eqP : forall T1 T2 : eqType, Equality.axiom (T:=T1 * T2) (pair_eq T1 T2).
Check @val_eqP  : forall (T : eqType) (P : pred T) (sT : subType (T:=T) P),
    Equality.axiom (T:=sT) (fun x y : sT => val x == val y).
Check @val.

(* eqの成立する証明 *)
Print prod_eqMixin.                         (* pair_eqP *)
(* 以下はサブタイプであることを使う。 *)
Print tuple_eqMixin.  (* (@val_eqP (seq_eqType T) (fun x : seq T => size x == n) (tuple_subType n T)) *)
Print ordinal_eqMixin. (* (@val_eqP nat_eqType (fun x : nat => x < n) (ordinal_subType n)) *)
Print finfun_eqMixin. (* (@val_eqP (tuple_eqType #|aT| rT) xpredT (finfun_subType aT rT)) *)
Print set_eqMixin.    (* (@val_eqP (finfun_of_eqType T bool_eqType) xpredT (set_subType T)) *)
Print perm_eqMixin.   (* (@val_eqP (finfun_of_eqType T T)
     (fun x : {ffun T -> T} => injectiveb (aT:=T) (rT:=T) x) 
     (perm_subType T)) *)


(* finType であること *)
Check FinMixin : forall (T : countType) (e : seq T),
    Finite.axiom (T:=T) e -> Finite.mixin_of T.
Print tuple_finMixin.  (* Eval hnf in FinMixin (@FinTuple.enumP n T) *)
Check fun (n : nat) (T : finType) => (@FinTuple.enumP n T).
Check @FinMixin.
Definition tuple_finMixin :=
  fun (n : nat) (T : finType) =>
        @FinMixin (tuple_countType n T) (FinTuple.enum n T) (@FinTuple.enumP n T).

(* Compute [finMixin of tuple_type aT rT by <:]. こんなものはない *)

Print ordinal_finMixin.  (* Eval hnf in UniqFinMixin ord_enum_uniq mem_ord_enum. *)
Print finfun_finMixin. (* fun aT rT : finType => [finMixin of finfun_type aT rT by <:] *)
Print set_finMixin.    (* fun T     : finType => [finMixin of set_type T by <:] *)
Print perm_finMixin.   (* fun T     : finType => [finMixin of perm_type T by <:] *)

Check {ffun bool -> bool}.
Check {ffun bool -> 3.-tuple bool}.
Check {ffun bool -> {set bool}}.
Check {ffun bool -> {perm bool}}.
Check {set {set {set bool}}}.

Print Canonical Projections.

Check fun (n : nat) (T : finType) =>
Finite.Mixin
  (T:=EqType (n.-tuple T)                   (* contType *)
        (Countable.class
           (Countable.Pack {| Countable.base := Choice.class (tuple_choiceType n T); Countable.mixin := tuple_countMixin n T |} (n.-tuple T))))
  (tuple_countMixin n T)                    (* seq T *)
  (mixin_enum:=FinTuple.enum n T)           (* axiom .... *)
  (FinTuple.enumP (n:=n) (T:=T))            (* mixin_of *)
.

(* **** *)
(* **** *)
(* **** *)

Variable   T1 T2 : eqType.
Definition pair_eq         := [rel u v : T1 * T2 | (u.1 == v.1) && (u.2 == v.2)].
Lemma      pair_eqP        : Equality.axiom pair_eq.
Definition prod_eqMixin    := Equality.Mixin pair_eqP.
Canonical  prod_eqType     := @Equality.Pack (T1 * T2) prod_eqMixin.

Structure  tuple_of n T    := Tuple { tval :> seq T; _ : size tval == n }.
Notation   "n .-tuple T"   := (tuple_of n T).
Canonical  tuple_eqType n T : eqType := Equality.Pack (Equality.Mixin (@eqtupleP n T)).
Canonical  tuple_subType   := Eval hnf in [subType for tval].
Definition tuple_eqMixin   := Eval hnf in [eqMixin of n.-tuple T by <:].
Canonical  tuple_eqType    := Eval hnf in EqType (n.-tuple T) tuple_eqMixin.
Canonical  tuple_subType   := Eval hnf in [subType for tval].
Definition tuple_enum (T : finType) n : seq (n.-tuple T) := pmap insub (all_words n (enum T)).
Lemma enumP T n : Finite.axiom (tuple_enum T n).
Definition tuple_finMixin  := Eval hnf in FinMixin (@FinTuple.enumP n T).
Canonical  tuple_finType   := Eval hnf in FinType (n.-tuple T) tuple_finMixin.
Definition tuple_enum (T : finType) n : seq (n.-tuple T) := pmap insub (all_words n (enum T)).

Lemma enumP T n : Finite.axiom (tuple_enum T n).
Definition mytype_finMixin := Finite.Mixin mytype_enum mytype_enumP.
Canonical  mytype_finType  := @Finite.Pack mytype mytype_finMixin.
Definition mytype_finMixin := Finite.UniqFinMixin myenum_uniq mem_myenum.

Inductive  ordinal (n : nat) : Type := Ordinal m of m < n.
Notation   "''I_' n"       := (ordinal n)
Coercion   nat_of_ord i    := let: @Ordinal m _ := i in m.
Canonical  ordinal_subType := [subType for nat_of_ord].
Definition ordinal_eqMixin := Eval hnf in [eqMixin of ordinal by <:].
Canonical  ordinal_eqType  := Eval hnf in EqType ordinal ordinal_eqMixin.
Definition ord_enum n : seq (ordinal n) := pmap insub (iota 0 n).
Definition ordinal_finMixin n := Eval hnf in UniqFinMixin (ord_enum_uniq n) (mem_ord_enum n).
Canonical  ordinal_finType n := Eval hnf in FinType (ordinal n) (ordinal_finMixin n)

Variables  (aT : finType) (rT : Type).
Inductive  finfun : Type   := Finfun of #|aT|.-tuple rT.
Definition fgraph f        := let: Finfun t := f in t.
Canonical  finfun_subType  := Eval hnf in [newType for fgraph].
Definition fun_of_fin aT rT f x := tnth (@fgraph aT rT f) (enum_rank x).
Coercion   fun_of_fin : finfun >-> FunClass.
Definition finfun aT rT f  := @Finfun aT rT (codom_tuple f).
Notation   "[ 'ffun' x : aT => F ]" := (finfun (fun x : aT => F)).
Definition finfun_eqMixin aT (rT : eqType) := Eval hnf in [eqMixin of finfun aT rT by <:].
Canonical  finfun_eqType   :=  Eval hnf in EqType (finfun aT rT) finfun_eqMixin.
Definition finfun_finMixin (aT rT : finType) := [finMixin of (finfun aT rT) by <:].
Canonical  finfun_finType  aT rT := Eval hnf in FinType (finfun aT rT) (finfun_finMixin aT rT).


Variable   T : finType.
Inductive  set_type : Type := FinSet of {ffun pred T}.
Definition finfun_of_set A := let: FinSet f := A in f.
Canonical  set_subType     := Eval hnf in [newType for finfun_of_set].
Definition set_eqMixin     := Eval hnf in [eqMixin of set_type by <:].
Canonical  set_eqType      := Eval hnf in EqType set_type set_eqMixin.
Definition set_finMixin    := [finMixin of set_type by <:].
Canonical  set_finType     := Eval hnf in FinType set_type set_finMixin.
Notation   "{ 'set' T }"   := (set_type T).

Inductive  perm_of (T : finType) : Type := Perm (pval : {ffun T -> T}) & injectiveb pval.
Definition pval p := let : Perm f _ := pinf.
Notation   "{ 'perm' T }"  := (perm_of T).
Canonical  perm_subType    := Eval hnf in [subType for pval].
Definition perm_eqMixin    := Eval hnf in [eqMixin of perm_type by <:].
Canonical  perm_eqType     := Eval hnf in EqType perm_type perm_eqMixin.
Definition perm_finMixin   := [finMixin of perm_type by <:].
Canonical  perm_finType    := Eval hnf in FinType perm_type perm_finMixin.
