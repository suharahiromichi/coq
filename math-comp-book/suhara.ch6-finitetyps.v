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
(* see also.
   An introduction to small scale reflection in Coq
   6. Finite objects in SSReflect
   http://hal.inria.fr/docs/00/55/53/79/PDF/main-rr.pdf
*)

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

Definition myenum := [:: false].

Lemma mytype_enumP : finite.axiom bool_eqType myenum.
Admitted.

(* Declare a finType *)

Definition mytype_finMixin := finite.Mixin bool_eqType myenum mytype_enumP.
Canonical mytype_finType := finite.Pack bool_eqType mytype_finMixin.
Print Canonical Projections.  
(* 
bool_eqType <- finite.sort ( mytype_finType )
mytype_finMixin <- finite.m ( mytype_finType )
 *)

(* Declare a finType *)

Lemma myenum_uniq : uniq myenum.
Proof.
Admitted.

Lemma mem_myenum : forall x, x \in myenum.
Proof.
Admitted.

Definition mytype_finMixin' :=
  finite.UniqFinMixin bool_eqType myenum myenum_uniq.

(* Some theory for finType *)
Lemma cardT (T : finType) : #|T| = size (enum T).
Proof.
Admitted.

Lemma forallP (T : finType) (P : pred T) : reflect (forall x, P x) [forall x, P x].
Proof.
Admitted.

(* END *)
