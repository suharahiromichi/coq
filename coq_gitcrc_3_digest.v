(**
A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3. Lost in Manhattan (抜萃)

Type Classを使って reflexivityとrewriteを拡張する。
ここでは、それに向かう説明だけを抄訳する。
*)

(* We consider the discrete plan the coordinate system of which 
    is based on Z *)
Require Import List.
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
Require Import Relations.
Require Import Setoid.

(**
3.2 Data Type and Definitions
 *)
(** Types for representing routes in the dicrete  plane *)
Inductive direction : Type := North | East | South | West.
Definition route := list direction.

Record Point : Type :=
  {
    Point_x : Z;
    Point_y : Z
  }.

Definition Point_O := Build_Point 0 0.

(**
3.3 Route Semantics
 *)
Definition translate (dx dy:Z) (P : Point) :=
  Build_Point (Point_x P + dx) (Point_y P + dy).

(** Equality test  between Points *)
Definition Point_eqb (P P':Point) :=
  Zeq_bool (Point_x P) (Point_x P') &&
           Zeq_bool (Point_y P) (Point_y P').

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

Definition route_equiv : relation route :=
  fun r r' => forall P:Point , move r P = move  r' P.
Infix "=r=" := route_equiv (at level 70):type_scope.

(**
3.4 On Route Equivalence
 *)
Lemma route_equiv_refl : reflexive _ route_equiv.
Proof.
  intros r p;
  reflexivity.
Qed.

Lemma route_equiv_sym : symmetric _ route_equiv.
Proof.
  intros r r' H p;
  symmetry; apply H.
Qed.

Lemma route_equiv_trans : transitive _ route_equiv.
Proof.
  intros r r' r'' H H' p;
  rewrite H;
  apply H'.
Qed.

Instance route_equiv_Equiv : Equivalence route_equiv.
Proof.
  split;
  [apply route_equiv_refl |
   apply route_equiv_sym |
   apply route_equiv_trans].
Qed.

(**
ここでできること（これは、route_equiv の定義だけで可能である）
・○ =r= ○ の reflexivityで、証明を終える。
・単独のをrewriteできる。
例：
r =r= r' のとき、
move r' P ---> move r P
 *)
(* Cons and app are Proper functions w.r.t. route_equiv *)
Lemma route_cons : forall r r' d, r =r= r' -> d::r =r= d::r'.
Proof. 
  intros r r' d H P;
  destruct d; simpl;
  rewrite H; reflexivity.
Qed.

(**
3.5 Proper Functions
*)
(* ************** ************* *)
(* cons に対して Propperである。 *)
(* ************** ************* *)
Require Import Morphisms.
Instance cons_route_Proper (d:direction): 
    Proper (route_equiv ==> route_equiv) (cons d) .
Proof.
  intros r r' H;
  apply route_cons;
  assumption.
Qed.

(**
ここでできること： consのtailをrewriteする。
例：
r =r= r' のとき、
South :: West :: r ---> South :: West :: r'
 *)

(**  cons_route_Proper allows to replace a route with an =r= equivalent one
     in a context composed by "cons" *)
Goal forall r r', r =r= r' ->
                  South::West::r =r= South::West::r'.
Proof.
  intros r r' H.
  rewrite H.
  reflexivity.
Qed.

(**
3.6 Some Other instances of Proper
*)
Lemma route_compose :
  forall r r' P, move (r ++ r') P = move r' (move r P).
Proof.
  induction r as [|d s IHs]; simpl;
  [auto | destruct d; intros;rewrite IHs;auto].
Qed.

Example Ex3 : forall r, North::East::South::West::r =r= r.
Proof.
  intros r P;
  destruct P; simpl. 
  unfold route_equiv, translate; simpl;
    do 2 f_equal; ring.
Qed.

Example Ex4 : forall r r', r =r= r' -> 
                North::East::South::West::r =r= r'.
Proof.
  intros r r' H.
  now rewrite Ex3.
Qed.

(* ************** *************** *)
(* append に対して Propperである。 *)
(* ************** *************** *)
Instance app_route_Proper :
  Proper (route_equiv==>route_equiv ==> route_equiv)
         (@app direction).
Proof. 
  intros r r' H r'' r''' H' P.
  repeat rewrite route_compose.
  rewrite H.
  rewrite H'.
  reflexivity.
Qed.

(**
ここでできること：appendの一部をrewriteする。
例：
North::East::South::West::r' =r= r' のとき、
r ++ North::East::South::West::r' ---> r ++ r'
 *)
Example Ex5 : forall r r',
                r ++ North::East::South::West::r' =r= r ++ r'.
Proof.
  intros r r'.
  now rewrite Ex3.
Qed.

(* END *)
