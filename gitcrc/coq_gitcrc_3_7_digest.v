(**
A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3. Lost in Manhattan (抜萃、つづき)

typeclassestut.pdf
typeclassesTut/Lost_in_NY.v

このうち、
3.7 Deciding Route Equivalence の Ex1'
を証明するまでを抜粋する。

3.7 では、それ以前の節の
「Type Classを使って reflexivityとrewriteを拡張する」
という内容とは打って変わって、起点と終点が同じなら、同じルートであること、
to prove some path equivalences through a simple computation
を説明している。

つまり、3.7で証明したことだけを使うなら、ルートの中に変数が含まれていてはいけない。
しかし、そうでない場合は、a simple computation になる。
*)

(* We consider the discrete plan the coordinate system of which 
    is based on Z *)
Require Import List.
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
Require Import Relations.
Require Import Setoid.

Require Import coq_gitcrc_3_digest.
(*************************************************************
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
*************************************************************)

(**
3.7 Deciding Route Equivalence
*)

(* Prove the correctness of Point_eqb *)
Lemma Point_eqb_correct :
  forall p p',
    Point_eqb p p' = true <-> p = p'.
Proof.
  destruct p; destruct p'; simpl; split.
  unfold Point_eqb;  simpl;  rewrite andb_true_iff; destruct 1.
  repeat rewrite <- Zeq_is_eq_bool in *.
  rewrite H, H0; reflexivity.
  injection 1; intros H0 H1; rewrite H0, H1; unfold Point_eqb; simpl;
  rewrite andb_true_iff; repeat rewrite <- Zeq_is_eq_bool; now split.
Qed.

Lemma translate_comm :
  forall dx dy dx' dy' P,
    translate dx dy (translate dx' dy' P) = translate dx' dy' (translate dx dy P).
Proof.
  unfold translate; simpl; intros; f_equal; ring.
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
  split; intro H.
  rewrite H; trivial.
  intro P; replace P with (translate (Point_x P) (Point_y P) Point_O).
  repeat rewrite move_translate.
  rewrite H; reflexivity.
  destruct P; simpl; unfold translate; f_equal.
Qed.

Definition route_eqb r r' : bool :=
  Point_eqb (move r Point_O) (move r' Point_O).

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

(*****************
オリジナル文書にはない補足説明
@suharahiromichi

route_equiv と route_eqb は、reflect の関係にあるので、それを証明すれば、
Ex1 の =r= (route_equiv) を route_eqb にして証明することができる。

SSReflectの上で、Morphisms を使うのは難しそうなので、
ここで、試験的に局所的にSSReflectをImportしている。
******************
*)
Section SSR.
  Require Import ssreflect ssrbool.
  
  Lemma route_equivP (r r' : route) :
    reflect (route_equiv r r') (route_eqb r r').
  Proof.
    apply: (@iffP (route_eqb r r')).
    - by apply: idP.
    - by apply (route_equiv_equivb r r').
    - by apply (route_equiv_equivb r r').
  Qed.
  
  Example Ex1'' : East::North::West::South::East::nil =r= East::nil.
  Proof.
    apply/route_equivP.
      by [].
  Qed.
End SSR.

(* END *)
