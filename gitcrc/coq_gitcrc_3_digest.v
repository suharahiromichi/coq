(**
A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3. Lost in Manhattan (抜萃)

Coqのrewriteタクティックは Leibniz equality より弱い関係に関しても使えて便利だ。
ここでは、Type Classを使ってrewriteを拡張する説明を抄訳する。

typeclassestut.pdf
typeclassesTut/Lost_in_NY.v
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
(* Types for representing routes in the dicrete  plane *)
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

(* Equality test  between Points *)
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
Infix "=r=" := route_equiv (at level 70) : type_scope.

(**
ここでできること。
・route_equiv の定義による書き換え。
例： r =r= r' のとき、
move r' P ---> move r P
 *)

Goal forall r r' P, r =r= r' -> move r P = move r' P.
Proof.
  intros r r' P H.
  rewrite H.
  reflexivity.
Qed.

(* Cons and app are Proper functions w.r.t. route_equiv *)
Lemma route_cons : forall r r' d, r =r= r' -> d::r =r= d::r'.
Proof. 
  intros r r' d H P;
  destruct d; simpl;
  rewrite H; reflexivity.                   (* move r _ = move r' _ *)
Qed.

(* 問題番号は、PDFテキストではなく、サンプルソースにあわせている。 *)
Example Ex1 : East::North::West::South::East::nil =r= East::nil.
Proof.
  intro P; destruct P; simpl.
  unfold route_equiv, translate; simpl; f_equal; ring.
Qed.

(**
3.4 On Route Equivalence
 *)
Lemma route_equiv_refl : reflexive route route_equiv.
Proof.
  intros r p;
  reflexivity.
Qed.

Lemma route_equiv_sym : symmetric route route_equiv.
Proof.
  intros r r' H p;
  symmetry; apply H.
Qed.

Lemma route_equiv_trans : transitive route route_equiv.
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
ここでできること
・○ =r= ○ の reflexivity。
 *)
Goal forall r, r =r= r.
Proof. 
  reflexivity.
Qed.

Example Ex2 :
  South::East::North::West::South::East::nil =r= South::East::nil.
Proof.
  apply route_cons; apply Ex1.
Qed.

(**
3.5 Proper Functions
*)
(***************************************************)
(* cons d は、 route_equiv に対して Propperである。 *)
(***************************************************)
Require Import Morphisms.
Locate "_ ==> _".

Instance cons_route_Proper (d : direction) :
  Proper (route_equiv ==> route_equiv) (cons d) .
Proof.
  intros r r' H;
  apply route_cons;
  assumption.
Qed.

(**
ここでできること：
consのtailをrewriteする（route_consによる）。
例：
r =r= r' のとき、
d :: r ---> d :: r'
 *)

(* cons_route_Proper allows to replace a route with an =r= equivalent one
     in a context composed by "cons" *)
Goal forall r r', r =r= r' ->
                  South::West::r =r= South::West::r'.
Proof.
  intros r r' H.
  rewrite H.
  reflexivity.
Qed.

Lemma route_cons' : forall r r' d, r =r= r' -> d::r =r= d::r'.
Proof. 
  intros r r' d H.
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

Example Ex4 : forall r r', r =r= r' -> North::East::South::West::r =r= r'.
Proof.
  intros r r' H.
  now rewrite Ex3.
Qed.

(**************************************************)
(* append は、route_equiv に対して Propperである。 *)
(**************************************************)
Instance app_route_Proper :
  Proper (route_equiv ==> route_equiv ==> route_equiv)
         (@app direction).
Proof. 
  intros r r' H r'' r''' H' P.
  repeat rewrite route_compose.
  rewrite H.
  rewrite H'.
  reflexivity.
Qed.

(**
ここでできること：appendの一部をrewriteする
（route_composeによる）。
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

(**
おまけ
*)
(***************************************************************)
(* move は、route_equi と (Leibniz) eq に対して Propperである。 *)
(***************************************************************)
Instance move_Proper :
  Proper (route_equiv ==> @eq Point ==> @eq Point) move . 
Proof.
  intros r r' Hr_r' p q Hpq.
  rewrite Hpq; apply Hr_r'.
Qed.

(**********************************************************************)
(* length は、 route_equi と (Leibniz) eq に対して Propperで「ない」。 *)
(**********************************************************************)
Example length_not_Proper :
  ~Proper (route_equiv ==> @eq nat) (@length _).
Proof.
  intro H; generalize (H (North::South::nil) nil); simpl; intro H0.
  discriminate H0.
  intro P;destruct P; simpl;
  unfold translate; simpl; f_equal; simpl; ring.
Qed.

(* 3.7 節は以下に移動した。 *)
(*
https://github.com/suharahiromichi/coq/blob/master/gitcrc/coq_gitcrc_3_7_digest.v
*)

(* END *)
