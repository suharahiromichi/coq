From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Generalizable All Variables. *)
Require Import Aw_0_Notations.
Require Import Aw_1_3_Categories.
Require Import Aw_1_4_Functors.
Require Import Aw_1_5_Isomorphisms.

(******************************************************************************)
(* Chapter 2.2: Initial and Terminal Objects                                  *)
(******************************************************************************)

Generalizable Variables a.

Class InitialObject `{C : Category} (initial_obj : C) :=
  {
    zero          := initial_obj;
    bottom        : forall a, zero ~> a;
    bottom_unique : forall `(f : zero ~> a), f === (bottom a)
  }.
Notation "? A" := (bottom A)     : category_scope.
Notation "0"   := zero           : category_scope.
Coercion zero : InitialObject >-> obj.
Implicit Arguments InitialObject [[Obj] [Hom]].

Class TerminalObject `{C : Category} (terminal_obj : C) :=
  {
    one         := terminal_obj;
    drop        : forall a,  a ~> one;
    drop_unique : forall `(f : a ~> one), f === (drop a)
  }.
Notation "! A" := (drop A)       : category_scope.
Notation "1"   := one            : category_scope.
Coercion one : TerminalObject >-> obj.
Implicit Arguments TerminalObject [[Obj] [Hom]].

About InitialObject.
About TerminalObject.

(* initial objects are unique up to iso *)
(* 始対象は同型を除いて一意 *)
Lemma initial_unique_up_to_iso `{C : Category}
      {io1 : C} (i1 : InitialObject C io1)
      {io2 : C} (i2 : InitialObject C io2) : io1 ≅ io2.
Proof.
  refine {|
      iso_backward := bottom(InitialObject := i2) io1;
      iso_forward  := bottom(InitialObject := i1) io2
    |}.
  Check (bottom_unique(InitialObject := i1)).
  - setoid_rewrite (bottom_unique(InitialObject := i1)).
    reflexivity.
  - setoid_rewrite (bottom_unique(InitialObject := i2)).
    reflexivity.
Qed.

(* terminal objects are unique up to iso *)
(* 終対象は同型を除いて一意 *)
Lemma terminal_unique_up_to_iso `{C : Category}
      {to1 : C} (t1 : TerminalObject C to1)
      {to2 : C} (t2 : TerminalObject C to2) : to1 ≅ to2.
Proof.
  refine {|
      iso_backward := drop(TerminalObject := t1) to2;
      iso_forward  := drop(TerminalObject := t2) to1
    |}.
  - setoid_rewrite (drop_unique(TerminalObject := t1)).
    reflexivity.
  - setoid_rewrite (drop_unique(TerminalObject := t2)).
    reflexivity.
Qed.

(* END *)
