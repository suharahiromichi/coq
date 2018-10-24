(* "Type Classes for Mathematics in Type Theory" の Category の定義 *)

Global Generalizable All Variables.

Require Import Relations.
(* Require Import Setoid. *)
Require Import Morphisms.                   (* Proper *)

Class Equiv A := equiv : relation A.

Class Arrows (O : Type) : Type := Arrow : O -> O -> Type.

Notation "A == B" := (equiv A B) (at level 55, right associativity).
Notation "A --> B" := (Arrow A B) (at level 55, right associativity).

Class CatId O `{Arrows O} := cat_id : `(x --> x).
Class CatComp O `{Arrows O} :=
  comp : forall {x y z}, (y --> z) -> (x --> y) -> (x --> z).

Notation "A \o B" := (comp A B) (at level 40, left associativity).

Class Setoid A {Ae : Equiv A} : Prop := setoid_eq :> Equivalence (@equiv A Ae).

Notation "(=)" := equiv.

Class Category (O : Type) `{!Arrows O} `{forall x y : O, Equiv (x --> y)}
      `{!CatId O} `{!CatComp O} : Prop :=
  {
    arrow_equiv :> forall x y, Setoid (x --> y);
    
    comp_assoc w x y z (a : w --> x) (b : x --> y) (c : y --> z) :
      c \o (b \o a) = (c \o b) \o a;
    comp_proper :> forall x y z, Proper ((=) ==> (=) ==> (=)) (@comp _ _ _ x y z);
    id_l `(a : x --> y) : cat_id y \o a = a;
    id_r `(a : x --> y) : a \o cat_id x = a;
  }.

(* END *)
