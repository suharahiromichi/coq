(*
A Gentle Introduction to Type Classes and Relations in Coq
の Chapter 3. を SSReflectで書いてみた。

SSReflectなので、route_eqb が中心となり =r== で表す。
*)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly ssrnum ssrint rat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Types for representing routes in the dicrete  plane *)

Inductive direction : Type :=
  North | East | South | West.
Definition route := list direction.

Record Point : Type :=
  {
    Point_x : int; 
    Point_y : int
  }.

Definition Point_O := Build_Point 0 0.

Definition translate (dx dy : int) (P : Point) :=
  Build_Point (Point_x P + dx) (Point_y P + dy).

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

(*  move P r follows the route r starting from P *)

Fixpoint move (r : route) (P : Point) : Point :=
 match r with
 | nil => P
 | North :: r' => move r' (translate 0 1 P)
 | East :: r' => move r' (translate 1 0 P) 
 | South :: r' => move r' (translate 0 (-1) P)
 | West :: r' => move r' (translate (-1) 0 P)
 end.

(* We consider that two routes are "equivalent" if they define
  the same moves. For instance, the routes
  East::North::West::South::East::nil and East::nil are equivalent *)

(* これは、SSReflect の rel ではない。 *)
Definition route_equiv (r r' : route) :=
  forall (P : Point), Point_eqb (move r P) (move  r' P).
Check route_equiv : route -> route -> Prop.
Infix "=r=" := route_equiv (at level 70):type_scope.

(* Point_O が固定であることに注意。ここでは、このboolを中心に使っていく。 *)
Definition route_eqb (r r' : route) :=
  Point_eqb (move r Point_O) (move  r' Point_O).
Check route_eqb : route -> route -> bool.
Check route_eqb : rel route.
Infix "=r==" := route_eqb (at level 70):type_scope. (* ！注意！ *)

Example Ex1' : East::North::West::South::East::nil =r== East::nil.
Proof.
  by [].
Qed.

Check rel route.
Check reflexive.
Check reflexive route_eqb.
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

Lemma route_eqb_Eqb : equivalence_rel route_eqb.
Proof.
  split.
  - apply: route_eqb_refl.
  - move=> H1.
    apply/idP/idP => H2.
    Check @route_eqb_trans x y z.
    + apply: (@route_eqb_trans x y z).
      Check @route_eqb_sym y x.
      * by rewrite (@route_eqb_sym y x).
      * by apply: H2.
    Check @route_eqb_trans y x z.
    + apply: (@route_eqb_trans y x z).
      * by apply: H1.
      * by apply: H2.
Qed.

(* これだけ、=r= を使う。 *)
Lemma route_cons : forall r r' d, r =r= r' -> d::r =r= d::r'.
Proof. 
  move=> r r' d H.
  rewrite /route_equiv in H.
  rewrite /route_equiv.
  move=> P.
  case: d.
  by rewrite (H (translate 0 1 P)).
  by rewrite (H (translate 1 0 P)).
  by rewrite (H (translate 0 (-1) P)).
  by rewrite (H (translate (-1) 0 P)).
Qed.

Example Ex2' : South::East::North::West::South::East::nil =r== South::East::nil.
Proof.
  (* apply: route_cons. *)
  by apply: Ex1'.
Qed.

Example Ex3' : forall r, North::East::South::West::r =r== r.
Proof.
  move=> r.
  apply/PointEqP.
  by rewrite //=.
Qed.

Example Ex3 : forall r, North::East::South::West::r =r= r.
Proof.
  move=> r.
  rewrite /route_equiv /translate /=.
  move=> P.
  apply/PointEqP.
  f_equal.
  rewrite /translate //=.
  have H1 : forall (x : int), x + 0 + 1 + 0 - 1 = x.
    by admit.
  have H2 : forall (y : int), y + 1 + 0 - 1 + 0 = y.
    by admit.
  rewrite (H1 (Point_x P)).
  rewrite (H2 (Point_y P)).
(*  {| Point_x := Point_x P; Point_y := Point_y P |} = P *)
  admit.
Qed.

Example Ex4' : forall r r', r =r== r' -> 
                North::East::South::West::r =r== r'.
Proof.
  by [].
Qed.

Example Ex5 : forall r r',  r ++ North::East::South::West::r' =r= r ++ r'.
Proof.
  move=> r r'.
  rewrite Ex3.
  admit.
Qed.

(* *************** *)

Lemma route_equiv_Origin (r r' : route) :
  forall r r', r =r= r' <-> move r Point_O = move r' Point_O .
Proof.
  admit.
Qed.

Lemma route_equiv_equivb (r r' : route) :
  route_equiv r r' <-> route_eqb r r' = true.
Proof.
  admit.
Qed.


(* END *)
