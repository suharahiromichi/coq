Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg div ssrnum ssrint.
Open Scope int_scope.
Import intZmod.                             (* addz *)

Locate "_ + _".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3. Lost in Manhattan
を SSReflectで書いてみた。

3.7 Deciding Route Equivalence
のEx1'の証明ができることを目標とする。

@suharahiromichi
*)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly ssrnum ssrint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope int_scope.
Delimit Scope int_scope with Z.
Local Open Scope int_scope.

(**
3.2 Data Types and Definitions
*)
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

(**
3.3 Route Semantics
 *)
Definition translate (dx dy : int) (P : Point) :=
  Build_Point (Point_x P + dx) (Point_y P + dy).

(** Equality test  between Points *)
Definition Point_eqb (P P': Point) : bool :=
  (Point_x P == Point_x P') &&
  (Point_y P == Point_y P').

(*  move P r follows the route r starting from P *)
Fixpoint move (r:route) (P:Point) : Point :=
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


Lemma Point_eqb_correct' :
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
  - by rewrite (Point_eqb_correct' p p').
  - by rewrite (Point_eqb_correct' p p').
Qed.

(* Point_eqb_correct の別の証明 *)
(* バニラCoqの andb_true_iff だが、andP を直接使えばよい。 *)
Lemma andb_true_iff :
  forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  move=> b1 b2.
  split => H.
  by apply/andP.
  by apply/andP.
Qed.
(* notu *)

Lemma int_eq_bool (a b : int) :
  (a == b) = true <-> a = b.
Proof.
  admit.
Qed.

Lemma int_eq_boolP (a b : int) :
  reflect (a = b) (a == b).
Proof.
  admit.
Qed.

(* Prove the correctness of Point_eqb *)
Lemma Point_eqb_correct :
  forall p p', Point_eqb p p' = true <-> p = p'.
Proof.
  move=> p p'.
  elim: p; elim: p'; split.
  - rewrite /Point_eqb //=.
    move/andP.
    elim.
    move/int_eq_boolP => H1.
    move/int_eq_boolP => H2.
      by rewrite H1; rewrite H2.
  - elim.
    rewrite /Point_eqb //=.
    apply/andP.
    split.
      by apply/int_eq_boolP.
      by apply/int_eq_boolP.
Qed.      

(* *************************** *)

(* Point_O が固定であることに注意。ここでは、このboolを中心に使っていく。 *)
Definition route_eqb r r' : bool :=
  Point_eqb (move r Point_O) (move r' Point_O).
Infix "=r==" := route_eqb (at level 70):type_scope.

Example Ex1'' : East::North::West::South::East::nil =r== East::nil.
Proof.
  apply Point_eqb_correct.
  by [].
Qed.

(* *************************** *)
(**
3.4 On Route Equivalence 
*)
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

(* route_eqb (=r==) を使う場合。 *)
Example Ex2' : South::East::North::West::South::East::nil =r== South::East::nil.
Proof.
  (* apply: route_cons. *)
  by apply: Ex1''.
Qed.

Example Ex3' : forall r, North::East::South::West::r =r== r.
Proof.
  move=> r.
  apply/PointEqP.
  by rewrite //=.
Qed.

Example Ex4' : forall r r', r =r== r' -> 
                North::East::South::West::r =r== r'.
Proof.
  by [].
Qed.

(* ****************** *)
(* route_equiv と route_eqb の reflect を証明する *)
(* ****************** *)

(* これは、SSReflect の rel ではない。 *)
Definition route_equiv (r r' : route) :=
  forall (P : Point), (move r P) = (move  r' P).
Check route_equiv : route -> route -> Prop.
Infix "=r=" := route_equiv (at level 70):type_scope.

(**
3.6 Some Other instances of Proper
*)
Lemma route_compose :
  forall r r' P, move (r ++ r') P = move r' (move r P).
Proof.
  induction r as [|d s IHs]; simpl;
  [auto | destruct d; intros;rewrite IHs;auto].
Qed.

(*
Example Ex3 : forall r, North::East::South::West::r =r= r.
Proof.
  intros r P;
    destruct P; simpl.
  unfold route_equiv, translate; simpl;
    do 2 f_equal; ring.
Qed.
*)

Lemma addrC (a b c : int) :
  (a + b + c)%R = (a + c + b)%R.
Proof.
  admit.
Qed.

Lemma add0r (a : int) :
  (0 + a)%R = a%R.
Proof.
  admit.
Qed.

Lemma translate_comm :
  forall dx dy dx' dy' P,
    translate dx dy (translate dx' dy' P) = translate dx' dy' (translate dx dy P).
Proof.
  rewrite /translate //=.
  move=> dx dy dx' dy' P.
  apply Point_eqb_correct'.
  rewrite /Point_eqb //=.
  apply/andP.
  split.
  by rewrite addrC.
  by rewrite addrC.
Qed.

Lemma move_translate :
  forall r P dx dy,
    move r (translate dx dy P) = translate dx dy (move r P).
Proof.
  induction r as [|a r]; simpl; [reflexivity|].  
  destruct a;simpl; intros;rewrite <- IHr;rewrite  (translate_comm); auto.
Qed.

Lemma move_comm :
  forall r r' P,
    move r (move r' P) =  move r' (move r P).
Proof.
  induction r as [| a r']; [reflexivity|].
  simpl; destruct a;
  intros; repeat rewrite move_translate; rewrite IHr'; auto.
Qed.

Lemma app_comm : forall r r', r++r' =r=  r'++r.
Proof.
  intros r r' P; repeat rewrite route_compose; apply move_comm.
Qed.

(** the following lemma  will be used for deciding route equivalence *)
Lemma route_equiv_Origin :
  forall r r', r =r= r' <-> move r Point_O  = move r' Point_O .
Proof.
  move=> r r'.
  split; intro H.
  rewrite H; trivial.
  intro P; replace P with (translate (Point_x P) (Point_y P) Point_O).
  repeat rewrite move_translate.
  rewrite H; reflexivity.
  destruct P; simpl; unfold translate; f_equal; simpl.
  by rewrite add0r.
  by rewrite add0r.
Qed.

(**  ... we can now prove route_eqb's  correctness *)
Lemma route_equiv_equivb :
  forall r r',
    route_equiv r r' <-> route_eqb r r' = true.
Proof.
  intros r r'; rewrite route_equiv_Origin;
  unfold route_eqb; rewrite Point_eqb_correct; tauto.
Qed.

Ltac route_eq_tac := rewrite route_equiv_equivb; reflexivity.

(** another proof of Ex1, using computation  *)
Example Ex1' : East::North::West::South::East::nil =r= East::nil.
Proof.
  route_eq_tac.
Qed.

Lemma route_equivP (r r' : route) :
  reflect (route_equiv r r') (route_eqb r r').
Proof.
  apply: (@iffP (route_eqb r r')).
  - by apply: idP.
  - by apply (route_equiv_equivb r r').
  - by apply (route_equiv_equivb r r').
Qed.

Example Ex1 : East::North::West::South::East::nil =r= East::nil.
Proof.
  apply/route_equivP.
  by [].
Qed.

(* Ex5 は、=r= による rewrite を使うので、この範囲では解けない。 *)
Example Ex5' : forall r r',  r =r= r' -> r ++ North::East::South::West::r' =r= r ++ r'.
Proof.
  move=> r r' H.
  (* rewrite H. *)
  admit.
Qed.

(* END *)
