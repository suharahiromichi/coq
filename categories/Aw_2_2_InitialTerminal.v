From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Generalizable All Variables. *)
Require Import Aw_0_Notations.
Require Import Aw_1_3_Categories.
Require Import Aw_1_5_Isomorphisms.

(******************************************************************************)
(* Chapter 2.2: Initial and Terminal Objects                                  *)
(******************************************************************************)

Generalizable Variables a.

Class InitialObject `{C : Category} (initial_obj : C) :=
  {
    zero          := initial_obj;
    bottom        : forall a, zero ~> a;
    bottom_unique : forall `(f : zero ~> a), f === bottom a
  }.
Notation "? A" := (bottom A)     : category_scope.
Notation "0"   := zero           : category_scope.
Coercion zero : InitialObject >-> obj.
Implicit Arguments InitialObject [[Obj] [Hom]].

Class TerminalObject `{C : Category} (terminal_obj : C) :=
  {
    one         := terminal_obj;
    drop        : forall a,  a ~> one;
    drop_unique : forall `(f : a ~> one), f === drop a
  }.
Notation "! A" := (drop A)       : category_scope.
Notation "1"   := one            : category_scope.
Coercion one : TerminalObject >-> obj.
Implicit Arguments TerminalObject [[Obj] [Hom]].

About InitialObject.
About TerminalObject.

(* initial objects are unique up to iso *)
(* 始対象は同型を除いて一意 *)

(* 圏Cの対象io1とio2があり、それぞれ始対象としての性質を満たす。
このとき、io1とio2は同型である。 *)

(* オリジナルの証明 *)
Lemma initial_unique_up_to_iso'' `{C : Category}
      {io1 : C} (i1 : InitialObject C io1)
      {io2 : C} (i2 : InitialObject C io2) : io1 ≅ io2. (* Isomorphic io1 io2 *)
Proof.
  Check io1 : C : Category Hom.             (* 対象 *)
  Check i1 : InitialObject C io1 : Type.    (* 始対象としての性質 *)
  refine {|
      iso_backward := bottom(InitialObject := i2) io1;
      iso_forward  := bottom(InitialObject := i1) io2
    |}.
  - setoid_rewrite (bottom_unique(InitialObject := i1)).
    reflexivity.
  - setoid_rewrite (bottom_unique(InitialObject := i2)).
    reflexivity.
Qed.

(* rewriteを使い、省略の無い証明 *)
Program Instance initial_unique_up_to_iso' `{C : Category}
      {io1 : C} (i1 : InitialObject C io1)
      {io2 : C} (i2 : InitialObject C io2) : io1 ≅ io2.
Obligation 1.
Proof.                                      (* iso_forward *)
  (* io1 ~~{ C }~~> io2 *)
  Check bottom.
  Check @bottom.
  Check (@bottom Obj Hom C zero i1 io2).
  by apply (@bottom Obj Hom C zero i1 io2).
Qed.
Obligation 2.
Proof.                                      (* iso_backward *)
  (* io2 ~~{ C }~~> io1 *)
  by apply (@bottom Obj Hom C zero i2 io1).
Qed.
Obligation 3.
Proof.
  Check bottom_unique.
  Check @bottom_unique.
  Check (@bottom_unique Obj Hom C zero i1 io1).
  setoid_rewrite bottom_unique.
  Undo 1.
  
  (* 左辺 === bottom io1 *)
  Check (@bottom_unique Obj Hom C zero i1 io1
                        (initial_unique_up_to_iso'_obligation_2 i1 i2 \\o
                         initial_unique_up_to_iso'_obligation_1 i1 i2)).
  rewrite (@bottom_unique Obj Hom C zero i1 io1
                        (initial_unique_up_to_iso'_obligation_2 i1 i2 \\o
                         initial_unique_up_to_iso'_obligation_1 i1 i2)).
  
  (* 右辺 === bottom io1 *)
  Check (@bottom_unique Obj Hom C zero i1 io1 iid).
  rewrite (@bottom_unique Obj Hom C zero i1 io1 iid).
  reflexivity.
Qed.
Obligation 4.
Proof.
  setoid_rewrite bottom_unique.
  Undo 1.
  
  (* 左辺 === bottom io2 *)
  rewrite (@bottom_unique Obj Hom C zero i2 io2
                        (initial_unique_up_to_iso'_obligation_1 i1 i2 \\o
                         initial_unique_up_to_iso'_obligation_2 i1 i2)).
  (* 左辺 === bottom io2 *)
  rewrite (@bottom_unique Obj Hom C zero i2 io2 iid).
  reflexivity.
Qed.

(* 適度に省略した証明 *)
Program Instance initial_unique_up_to_iso `{C : Category}
      {io1 : C} (i1 : InitialObject C io1)
      {io2 : C} (i2 : InitialObject C io2) : io1 ≅ io2.
Obligation 1.
Proof.                                      (* iso_forward *)
    by apply bottom.
Qed.
Obligation 2.
Proof.                                      (* iso_backward *)
    by apply bottom.
Qed.
Obligation 3.
Proof.
  rewrite (bottom_unique (initial_unique_up_to_iso_obligation_2 i1 i2 \\o
                          initial_unique_up_to_iso_obligation_1 i1 i2)).
  Check (bottom_unique iid).       (* Checkの結果は気にしないこと。 *)
  rewrite (bottom_unique iid).
  reflexivity.
Qed.
Obligation 4.
Proof.
  rewrite (bottom_unique (initial_unique_up_to_iso_obligation_1 i1 i2 \\o
                          initial_unique_up_to_iso_obligation_2 i1 i2)).
  rewrite (bottom_unique iid).
  reflexivity.
Qed.

(* terminal objects are unique up to iso *)
(* 終対象は同型を除いて一意 *)
Program Instance terminal_unique_up_to_iso `{C : Category}
      {to1 : C} (t1 : TerminalObject C to1)
      {to2 : C} (t2 : TerminalObject C to2) : to1 ≅ to2.
Obligation 1.
Proof.
  by apply drop.
Qed.
Obligation 2.
Proof.
  by apply drop.
Qed.
Obligation 3.
Proof.
  rewrite (drop_unique (terminal_unique_up_to_iso_obligation_2 t1 t2 \\o
                        terminal_unique_up_to_iso_obligation_1 t1 t2)).
  rewrite (drop_unique iid).
  reflexivity.
Qed.
Obligation 4.
Proof.
  rewrite (drop_unique (terminal_unique_up_to_iso_obligation_1 t1 t2 \\o
                        terminal_unique_up_to_iso_obligation_2 t1 t2)).
  rewrite (drop_unique iid).
  reflexivity.
Qed.

(* END *)
