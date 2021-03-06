(**
A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3. Lost in Manhattan (抜萃)

The Coq system provides now some useful tools for considering relations and proper
functions, allowing to use the rewrite tactics for relations that are weaker than the
Leibniz equality.
Coqのrewriteタクティックは Leibniz equality より弱い関係に関しても使える。

ここでは、Type Classを使ってrewriteとreflexivityを拡張する説明を抄訳する。

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
(* 参考 *)
Require Import Permutation.

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
  intros r r' d H P.
  destruct d; simpl;
  rewrite H; reflexivity.                   (* move r _ = move r' _ *)
Qed.

(* 問題番号は、PDFテキストではなく、サンプルソースにあわせている。 *)
Example Ex1 : East::North::West::South::East::nil =r= East::nil.
Proof.
  intro P.
  unfold move, translate.
  simpl.
  f_equal.
  - ring.
  - ring.
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

Print Reflexive. (* Classで定義されているが、中身があるのでrecordではない。 *)
(*
fun (A : Type) (R : relation A) => forall x : A, R x x
: forall A : Type, relation A -> Prop.
 *)
Print Equivalence_Reflexive.
About Equivalence_Reflexive.
(* Reflexive の引数 R : releation A が generalized されている。 *)
(* ただし、これらは上のInstanceの定義がなくても成立する。 *)
Check Equivalence_Reflexive : Reflexive eq.
Check Equivalence_Reflexive : Reflexive route_equiv.
Check Equivalence_Reflexive : Reflexive PeanoNat.Nat.eqf. (* Permutation *)

(*
Add Parametric Relation (x1 : T1) …(xn : Tk) : (A t1 …tn) (Aeq t′1 …t′m)
 [reflexivity proved by refl]
 [symmetry proved by sym]
 [transitivity proved by trans]
 as id.
is equivalent to an instance declaration:

Instance (x1 : T1) …(xn : Tk) => id : @Equivalence (A t1 …tn) (Aeq t′1 …t′m) :=
 [Equivalence_Reflexive := refl]
 [Equivalence_Symmetric := sym]
 [Equivalence_Transitive := trans].
*)

(**
ここでできること
・○ =r= ○ の reflexivity, symmetry, transitivity タクティクを使う。
 *)
Goal forall r, r =r= r.
Proof. 
  symmetry.
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

(*
What we really need is to tell to 
the rewrite tactic how to use route_cons
(rewriteタクティクが、route_consをどのように使うか、)
for using an equivalence r =r= r'
(r =r= r' を使うために、)
for replacing r with r' in a term of the form cons d r
(cons d r の中の r を r' で置き換えるために、)
for proving directly the equivalence cons d r =r= cons d r'.
(cons d r =r= cons d r' を直接証明するために。)

「rewriteタクティクが、cons d r =r= cons d r' を直接証明するために、
cons d r の中の r を r' で置き換えるために、r =r= r' を使うために、route_consをどう使うか。」

In other words, we say that cons d is proper w.-r.-t. the relation route_equiv.
In Coq this fact can be declared as an instance of:

「cons d は、 route_equiv に対して Propperである。この事実は次のインスタンスで宣言できる」
*)
Instance cons_route_Proper (d : direction) :
  Proper (route_equiv ==> route_equiv) (cons d) .
(* ∀r r', r =r= r' -> cons d r =r= cons d r' *)
Proof.
  intros r r' H.
  apply route_cons.
  assumption.

  Restart.
  intros r r' H.
  rewrite (route_cons r r').                (* Leibniz equality *)
  - reflexivity.
  - assumption.
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
  intros r P.
  destruct P; simpl.
  unfold move, translate; simpl.
  f_equal.
  f_equal.
  - ring.
  - ring.
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
  Proper (route_equiv ==> route_equiv ==> route_equiv) (@app direction).
(* ∀r r' r'' r''', r =r= r'' -> r' =r= r''' -> r ++ r'' =r= r' ++ r''' *)
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
(* move は、route_equiv と (Leibniz) eq に対して Propperである。 *)
(***************************************************************)
Instance move_Proper :
  Proper (route_equiv ==> @eq Point ==> @eq Point) move . 
(* ∀r r' p q, r =r= r' -> p = q -> move r p = move r' q. 「=」はPointどうしのeq *)
Proof.
  intros r r' Hr_r' p q Hpq.
  rewrite Hpq; apply Hr_r'.
Qed.

(**********************************************************************)
(* length は、 route_equi と (Leibniz) eq に対して Propperで「ない」。 *)
(**********************************************************************)
Example length_not_Proper :
  ~Proper (route_equiv ==> @eq nat) (@length _).
(* ~ (∀r r', r =r= r' -> length r = length r'). 「=」はnatのeq *)
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
