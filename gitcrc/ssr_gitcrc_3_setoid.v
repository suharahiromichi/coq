(**
A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3. Lost in Manhattan (抜萃)
mathink さんの記事を参考に Setoid で実装する。

http://mathink.net/program/coq_setoid.html
https://gist.github.com/mathink/52ab4b2290722b9d8340
*)

Require Import Basics Tactics Setoid Morphisms.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype tuple finfun bigop prime ssralg poly ssrnum ssrint rat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Setoidの定義 *)
Structure Setoid :=
  {
    carrier:> Type;                         (* 型 *)
    equal: relation carrier;                (* 二項関係 *)
    prf_Setoid:> Equivalence equal          (* 同値関係 *)
  }.
Existing Instance prf_Setoid.
Notation Setoid_of eq := (@Build_Setoid _ eq _). (* 二項関係だけ与える *)
(* 型は推論されるが、同値関係は証明を要求される。 *)

(* SSReflectの==と衝突しないように===とする。 *)
Notation "(=== :> S )" := (equal (s:=S)).
Notation "(===)" := (=== :> _).
Notation "x === y :> S" :=
  (equal (s:=S) x y) (at level 70, y at next level, no associativity).
Notation "x === y" :=
  (x === y :> _) (at level 70, no associativity).

(* ************ *)
(* eq の Setoid *)
(* ************ *)
Program Canonical Structure eq_Setoid (A: Type) := Setoid_of (@eq A).

Eval simpl in 0 === 0.                      (* === の実体は = (eq) *)

(* ************************** *)
(* 関数の外延的等価性で Setoid *)
(* ************************** *)
Definition ext_eq (X Y: Type)(f g: X -> Y) :=
  forall (x: X), f x = g x.
Arguments ext_eq X Y / f g.

Program Canonical Structure fun_Setoid (X Y: Type): Setoid :=
  Setoid_of (@ext_eq X Y).
Next Obligation.
  split.
  - intros f x; reflexivity.
  - intros f g Heq x; rewrite Heq; reflexivity.
  - intros f g h Heqfg Heqgh x; rewrite (Heqfg x); apply Heqgh.
Qed.

Definition plus1 (n: nat): nat := n + 1.
Eval simpl in plus1 === S.                      (* === の実体は ext_eq *)
Goal plus1 === S.
Proof.
  admit.
Qed.

(* ************************************ *)
(* Lost in Manhattan の Point の Setoid *)
(* ************************************ *)
(* *************** *)
(* Point の Setoid *)
(* *************** *) 

(** Types for representing routes in the dicrete  plane *)
Record Point : Type :=
  {
    Point_x : int; 
    Point_y : int
  }.

(** Equality test  between Points *)
Definition Point_eqb (P P': Point) : bool :=
  (Point_x P == Point_x P') &&
  (Point_y P == Point_y P').

(* Prove the correctness of Point_eqb *)
Lemma Point_eqb_correct :
  forall p p', Point_eqb p p' <-> p = p'.
Proof.
  case=> x y.                               (* by p *)
  case=> x' y'.                             (* by p' *)
  split.
  (* -> *)
  rewrite /Point_eqb /=.
  move/andP => [] /eqP Hxx' /eqP Hyy'.
  by rewrite Hxx' Hyy'.
  (* <- *)
  rewrite /Point_eqb /=.
  case=> Hxx' Hyy'.
  by apply/andP; split; [rewrite Hxx' | rewrite Hyy'].
Qed.

Lemma PointEqP p p' : reflect (p = p') (Point_eqb p p').
Proof.
  apply: (@iffP (Point_eqb p p')).
  - by apply: idP.
  - by rewrite (Point_eqb_correct p p').
  - by rewrite (Point_eqb_correct p p').
Qed.

Program Canonical Structure point_eq_Setoid :=
  Setoid_of Point_eqb.
Next Obligation.
  split.
  - move=> //= x; by apply/PointEqP.
  - move=> //= x y. move/PointEqP => H. apply/PointEqP. by [].
  - move=> //= x y z.
    move/PointEqP => Hxy.
    move/PointEqP => Hyz.
    apply/PointEqP.
    by rewrite -Hyz.
Qed.

Eval simpl in Build_Point 1 1 === Build_Point 1 1.
(* === の実体は is_true (Point_eqb) *)
Goal Build_Point 1 1 === Build_Point 1 1.
Proof.
  by apply Point_eqb_correct.
Qed.

(* *************** *)
(* Route の Setoid *)
(* *************** *) 
Inductive direction : Type :=
  North | East | South | West.
(* Setoid の定義ができなくなるので、route型は使わない。 *)
(* Definition route := seq direction. *)

Definition translate (dx dy : int) (P : Point) :=
  Build_Point (Point_x P + dx) (Point_y P + dy).

Fixpoint move (r : seq direction) (P : Point) : Point :=
 match r with
 | nil => P
 | North :: r' => move r' (translate 0 1 P)
 | East :: r' => move r' (translate 1 0 P) 
 | South :: r' => move r' (translate 0 (-1) P)
 | West :: r' => move r' (translate (-1) 0 P)
 end.

Definition route_equiv (r r' : seq direction) :=
  forall (P : Point), (move r P) = (move  r' P).
Check route_equiv : seq direction -> seq direction -> Prop.

(* Point_O が固定であることに注意。ここでは、このboolを中心に使っていく。 *)
Definition Point_O := Build_Point 0 0.
Definition route_eqb (r r' : seq direction) :=
  Point_eqb (move r Point_O) (move  r' Point_O).
Check route_eqb : seq direction -> seq direction -> bool.
Check route_eqb : rel (seq direction).

Lemma route_eqb_refl : reflexive route_eqb.
Proof.
  move=> r.
  apply/andP; by [].
Qed.

Lemma route_eqb_sym : symmetric route_eqb.
Proof.
  move=> r y.
  rewrite /route_eqb.
  apply/idP/idP;
    move/PointEqP => H;
      by apply/PointEqP.
Qed.

Lemma route_eqb_trans : transitive route_eqb.
Proof.
  move=> r x z.
  rewrite /route_eqb.
  move/PointEqP => H1;
  move/PointEqP => H2;
  apply/PointEqP.
  by rewrite H1 H2.
Qed.

Program Canonical Structure route_eq_Setoid :=
  Setoid_of route_eqb.
Next Obligation.
  split.
  - move=> //= x. apply: route_eqb_refl.
  - move=> //= x y H. by rewrite route_eqb_sym.
  - move=> //= x y z. by apply: route_eqb_trans.
Qed.

Eval simpl in East::North::West::South::East::nil === East::nil.
(* === の実体は、is_true (route_eqb) *)
(* Setoid の定義がおかしいと、実体が単なる = になる。ここは確認すること。 *)
Example Ex1' : East::North::West::South::East::nil === East::nil.
Proof.
  by [].
Qed.

(* END *)
