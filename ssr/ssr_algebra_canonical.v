From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Print Graph.
Print Canonical Projections.

(*
Require Export Relation_Definitions.

From Coq.Classes Require Export Init Equivalence Morphisms.

Open Scope equiv_scope.    
Open Scope list_scope.
*)

Module Monoid.
  
  Record mixin_of (A : Type) :=
    Mixin {
        R : A -> A -> Prop;                 (* relation A *)
        op : A -> A -> A;
        unit : A;
        assoc : forall a b c, R (op a (op b c)) (op (op a b) c);
        unit_l : forall a, R (op a unit) a;
        unit_r : forall a, R (op unit a) a;
      }.
  
  Structure type :=
    Pack {
        sort :> Type;
        mixin : mixin_of sort;
      }.
(*  
  Variable A : Type.
  Variable a : type.
  Check sort a.
  Check unit (mixin a).
*)  
  Fixpoint op_list {a : type} (l : seq (sort a)) :=
    match l with
    | nil => unit (mixin a)
    | cons x l' => (op (mixin a)) x (op_list l')
    end.
  
End Monoid.

Coercion Monoid.sort : Monoid.type >-> Sortclass.
Notation MonoidMixin := Monoid.Mixin.
Notation monoidType := Monoid.type.
Notation MonoidType := Monoid.Pack.
Notation op_list := Monoid.op_list.

(*
Fixpoint op_list {A : monoidType} {unit : A} {op : A -> A -> A} (l : seq A) :=
  match l with
  | nil => unit
  | cons a l' => op a (@op_list A unit op l')
  end.
 *)

Check @op_list : forall a : monoidType, seq a -> a.
Check op_list : seq _ -> _.

Module CMonoid.

  Record mixin_of (A : Type) :=
    Mixin {
        op : A -> A -> A;
        comm : forall a b, op a b = op b a;
      }.

  Record class_of (A : Type) :=
    Class {
        base :> Monoid.mixin_of A;
        mixin : mixin_of A;
      }.
  
  Record type :=
    Pack {
        sort :> Type;
        class : class_of sort;
      }.
  
  Coercion monoidType (cT : type) := MonoidType (base (class cT)).

End CMonoid.

Coercion CMonoid.base : CMonoid.class_of >-> Monoid.mixin_of.
Coercion CMonoid.mixin : CMonoid.class_of >-> CMonoid.mixin_of.
Coercion CMonoid.sort : CMonoid.type >-> Sortclass.
Notation CMonoidMixin := CMonoid.Mixin.
Notation CMonoidClass := CMonoid.Class.
Notation cmonoidType := CMonoid.type.
Notation CMonoidType := CMonoid.Pack.
Canonical Structure CMonoid.monoidType.

(* ************ *)
(* nat Instance *)
(* ************ *)

Definition nat_monoidMixin :=
  @MonoidMixin nat eq addn 0 addnA addn0 add0n.
Canonical nat_monoidType :=
  @MonoidType nat nat_monoidMixin.

Definition nat_cmonoidMixin :=
  @CMonoidMixin nat addn addnC.
Definition nat_cmonoidClass :=
  @CMonoidClass nat nat_monoidMixin nat_cmonoidMixin.
Canonical nat_cmonoidType :=
  @CMonoidType nat nat_cmonoidClass.


(* sample MonoidType *)
Check 3 : nat_monoidType.
Check @op_list nat_monoidType [:: 3; 5] : nat_monoidType.
Eval compute in @op_list nat_monoidType [:: 3; 5]. (* 8 *)
Check op_list [:: 3; 5] : nat_monoidType.
Eval compute in op_list [:: 3; 5].          (* 8 *)


(* sample CMonoidType *)
Check 3 : nat_cmonoidType.

(* CMonoid に対して、op_list が定義されているわけではない。 *)
Fail Check @op_list nat_cmonoidType [:: 3; 5] : nat_cmonoidType.
Fail Eval compute in @op_list nat_cmonoidType [:: 3; 5].
(* Definition nat_monoidType とすると、ここでエラーになるので、
   nat_monoidType が使われているようにみられる。 *)
Check op_list [:: 3; 5] : nat_cmonoidType.
Eval compute in op_list [:: 3; 5].          (* 8 *)

Print Graph.
Print Canonical Projections.
(*
nat_monoidMixin <- Monoid.mixin ( nat_monoidType )
CMonoid.base <- Monoid.mixin ( CMonoid.monoidType )
nat <- Monoid.sort ( nat_monoidType )
CMonoid.sort <- Monoid.sort ( CMonoid.monoidType )
*)

(* END *)
