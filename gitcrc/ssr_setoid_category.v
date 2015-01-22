(**
@suharahiromichi

2015_01_22
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Require Import Basics Tactics Coq.Setoids.Setoid Morphisms.
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
Require Import div.

(**
# Setoid
 *)
Class Setoid (carrier : Type) : Type :=
  {
    equiv : carrier -> carrier -> Prop;
    (* *** *)
    prf_Setoid_ref :
      forall x : carrier, equiv x x;
    prf_Setoid_sym :
      forall x y : carrier, equiv x y -> equiv y x;
    prf_Setoid_trn :
      forall x y z : carrier, equiv x y -> equiv y z -> equiv x z
  }.

Definition arrow A B := A -> B.

Instance arrow_setoid : Setoid (arrow a b) :=
  {
    equiv f g := forall x, f x = g x
  }.
Proof.
  (* f g h は arrow a b とする。 *)
  (* f x = f x *)
  - move=> f x.
      by [].
  (* f x = g x -> g x = f x  *)
  - move=> f g H x.
      by rewrite (H x).
  (* f x = g x -> g x = h x -> f x = h x *)
  - move=> f g h H1 H2 x.
      by rewrite (H1 x) (H2 x).
Qed.    

(**
# Poset
*)
Class Poset (carrier : Type) : Type :=
  {
    rel_op : carrier -> carrier -> Prop;
    (* *** *)    
    refl (x : carrier) : rel_op x x;
    asym (x y : carrier) : rel_op x y -> rel_op y x -> x = y;
    trans (y x z : carrier) : rel_op x y -> rel_op y z -> rel_op x z
  }.

Lemma eqn_leq' : forall m n, m <= n -> n <= m -> m = n.
Proof.
  move=> m n.
  elim: m n => [|m IHm] [|n] //.
  move=> H1 H2; congr (_ .+1); move: H1 H2.
  by apply (IHm n).
Qed.

Instance nat_poset : Poset nat :=
  {
    rel_op x y := leq x y
  }.
Proof.
  (* x <= x *)
  - by [].
  (* x <= y -> y <= x -> x = y *)
  - by apply eqn_leq'.
  (* x <= y -> y <= z -> x <= z *)
  - by apply leq_trans.
Qed.

Require Import FunctionalExtensionality.
Instance arrow_poset : Poset (arrow a b) :=
  {
    rel_op f g := forall x, f x = g x
  }.
Proof.
  (* f g h は arrow a b とする。 *)
  (* f x = f x *)
  - move=> f.
      by [].
  (* f x = g x -> g x = f x -> f = g *)
  - move=> f g.
    move=> H1 H2.
    apply functional_extensionality => x.
      by rewrite H1.
  (* f x = g x -> g x = h x -> f x = h x *)
  - move=> f g h.
    move=> H1 H2 x.
      by rewrite H1 H2.
Qed.

(*****)
Class Category (obj : Type) (hom : obj -> obj -> Type) :=
  {
    morphisms :> forall a b, Setoid (hom a b);
    id : forall a, hom a a; 
    compose : forall a b c, hom a b -> hom b c -> hom a c;
    id_unit_left :
      forall a b (f : hom a b), compose f (id b) = f;
    id_unit_right :
      forall a b (f : hom a b), compose (id a) f = f;
    assoc :
      forall a b c d (f : hom a b) (g : hom b c) (h : hom c d),
        compose f (compose g h) = compose (compose f g) h
  }.
      
Notation " x ・ y" := (compose y x) (at level 40, left associativity).

Check Category arrow : Type.

Instance TYPE : Category arrow :=
  {
    morphisms a b := arrow_setoid;
    id a x := x;
    compose a b c f g := compose f g
  }.
(* 未完 *)


(* END *)
