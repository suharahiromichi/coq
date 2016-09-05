From mathcomp Require Import all_ssreflect.
(*
From mathcomp Require Import fintype.
Print FinMixin.
Check FinMixin.

Print FinType.
Check FinType _ _.

Print UniqFinMixin.
Check UniqFinMixin.
 *)

(* 6. Sub-Types Terms with properties *)
(* 6.3 Finite types and their theory *)

(* Before describing other sub-types we introduce the interface of
types equipped with a finite enumeration.
別のsub-typeを示す前に、有限列挙を備えた型のインターフェースを導入する。
*)

(* 本節には例題が無いので、bool の subtype として false だけからなる型を定義する例を使う。 *)

(* Interface for finite types *)
Notation count_mem x := (count [pred y | y == x]).
Print count_mem.
Check count_mem false [:: false].
Compute (count_mem false [:: false]).       (* 1 : nat *)

Module finite.
  Definition axiom (T : eqType) (e : seq T) :=
    forall x : T, count_mem x e = 1.

  Record mixin_of (T : eqType) :=
    Mixin {
        enum : seq T;
        a : axiom T enum;
      }.
  
  Record pack_of :=
    Pack {
        sort : eqType;
        m : mixin_of sort
      }.
  
  Lemma UniqFinMixin (T : eqType) (e : seq T) :
    uniq e -> e =i T -> mixin_of T.
  Proof.
  Admitted.
End finite.

(* mytype を定義する。 *)
Inductive mytype : Set :=
  false : mytype.

Definition eqMytype (x y : mytype) : bool :=
  match x, y with
    | false,  false  => Datatypes.true
  end.

Lemma mytype_eqP : forall (x y : mytype), reflect (x = y) (eqMytype x y).
Proof.
  move=> x y.
    by apply: (iffP idP); case: x; case: y.
Qed.

Definition mytype_eqMixin := @EqMixin mytype eqMytype mytype_eqP.
Canonical mytype_eqType := @EqType mytype mytype_eqMixin.
Print Canonical Projections.
(* mytype <- Equality.sort ( mytype_eqType ) *)

Definition myenum : seq mytype := [:: false].

Lemma mytype_enumP : finite.axiom mytype_eqType myenum.
Proof.
  rewrite /finite.axiom.
  by case => //=.
Qed.
(* mytype の定義終わり。 *)


(* Declare a finType *)

(* any finType is also an eqType (see the parameter of the mixin), and
that to declare a finType instance one can write: *)

Definition mytype_finMixin := finite.Mixin mytype_eqType myenum mytype_enumP.
Canonical mytype_finType := finite.Pack mytype_eqType mytype_finMixin.
Print Canonical Projections.  
(* 
mytype_eqType <- sort ( mytype_finType )
mytype_finMixin <- m ( mytype_finType )
 *)

(* Declare a finType *)

Lemma myenum_uniq : uniq myenum.
Proof.
  done.
Qed.

Lemma mem_myenum : forall (x : mytype), x \in myenum.
Proof.
  by case.
Qed.

Definition mytype_finMixin' :=
  finite.UniqFinMixin mytype_eqType myenum myenum_uniq.

(* Some theory for finType *)
Lemma cardT (T : finType) : #|T| = size (enum T).
Proof.
Admitted.

Lemma forallP (T : finType) (P : pred T) : reflect (forall x, P x) [forall x, P x].
Proof.
Admitted.

(* END *)
