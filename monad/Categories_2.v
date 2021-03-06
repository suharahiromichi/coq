(* Steve Awodey's book on category theory *)
(******************************************************************************)
(* Chapter 1.3: Categories                                                    *)
(******************************************************************************)
(* @suharahiromichi *)

(*
(1) ベースライン
http://www.megacz.com/berkeley/coq-categories/
これをもとに改変。Instance ... Proper を使うようにした。
 *)

(*
(2) Proper関数の定義
A Gentle Introduction to Type Classes and Relations in Coq
*)

(*
(3) Setoid を使うようにし、Setsと(P,<=)のインスタンスをつくる。
http://www.iij-ii.co.jp/lab/techdoc/category/category1.html
 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import finset fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Notations.
Require Import Morphisms.
Require Import Coq.Setoids.Setoid.

(*
Reserved Notation "x ~> y" (at level 51, left associativity).
*)
Reserved Notation "x \\o y" (at level 51, left associativity).
Reserved Notation "x === y" (at level 71, left associativity).

Generalizable Variables a b c d e.

Class Setoid :=
  {
    carrier : Type;
    eqv : carrier -> carrier -> Prop;
    eqv_equivalence : Equivalence eqv
  }.
Coercion carrier : Setoid >-> Sortclass.
Notation "x === z" := (eqv x z).

Class Category (Obj : Type) (Hom : Obj -> Obj -> Setoid) :=
  {
    hom := Hom where "a ~> b" := (hom a b);
    ob  := Obj;
    id   : forall {a : Obj}, (a ~> a);
    comp : forall {a b c : Obj},
             (a ~> b) -> (b ~> c) -> (a ~> c)
                                       where "f \\o g" := (comp f g);
    comp_respects   : forall {a b c : Obj},
                        Proper (@eqv (a ~> b) ==> @eqv (b ~>c) ==> @eqv (a ~> c)) comp;
    left_identity   : forall `(f : a ~> b), id \\o f === f;
    right_identity  : forall `(f : a ~> b), f \\o id === f;
    associativity   : forall `(f : a ~> b) `(g : b ~> c) `(h : c ~> d),
                        f \\o g \\o h === f \\o (g \\o h)
}.
Coercion ob : Category >-> Sortclass.

Notation "a ~> b"       := (hom a b).
Notation "f === g"      := (eqv f g).
Notation "f \\o g"      := (comp f g).
(* Notation "a ~~{ C }~~> b" := (@hom _ _ C a b). *)

Generalizable Variables Obj Hom Prod.

(* eqv が、Reflexive と Symmetric と Transitive とを満たす。 *)
Instance category_eqv_Equiv `(C : Category Obj) (a b : Obj) :
  Equivalence (@eqv (a ~> b)).
Proof.
  by apply eqv_equivalence.
Qed.

(* comp は eqv について固有関数である。 *)
Instance category_comp_Proper `(C : Category Obj) (a b c : Obj) :
  Proper (@eqv (a ~> b) ==> @eqv (b ~>c) ==> @eqv (a ~> c)) comp.
Proof.
  by apply comp_respects.
Qed.


(* 可換性についての定理を証明する。 *)
Lemma juggle1 : forall `{C : Category}
                       `(f : a ~> b) `(g : b ~> c) `(h : c ~> d) `(k : d ~> e),
                  f \\o g \\o h \\o k === f \\o (g \\o h) \\o k.
Proof.
  intros.
  Check associativity f g h.
  rewrite <- associativity.
  reflexivity.
Defined.

Lemma juggle2 : forall `{C : Category}
                       `(f : a ~> b) `(g : b ~> c) `(h : c ~> d) `(k : d ~> e),
                  f \\o (g \\o (h \\o k)) === f \\o (g \\o h) \\o k.
Proof.
  intros.
  do ! rewrite <- associativity.
  reflexivity.
Defined.

Lemma juggle3 : forall `{C : Category}
                       `(f : a ~> b) `(g : b ~> c) `(h : c ~> d) `(k : d ~> e),
                  f \\o g \\o (h \\o k) === f \\o (g \\o h) \\o k.
Proof.
  intros.
  do ! rewrite <- associativity.
  reflexivity.
Defined.

Reserved Notation "x &&& y" (at level 50, left associativity).

(* 直積 *)
Class Product `{CP : Category Obj}
      `(proj1 : forall {a b : Obj}, (Prod a b) ~> a)
      `(proj2 : forall {a b : Obj}, (Prod a b) ~> b) :=
  {
    (* 仲介射 *)
    mediating : forall {a b x : Obj},
                  (x ~> a) -> (x ~> b) -> (x ~> (Prod a b))
                                            where "f &&& g" := (mediating f g);
    
    med_commute1 : forall (a b x : Obj) (f : x ~> a) (g : x ~> b),
                     (f &&& g) \\o proj1 === f;
    med_commute2 : forall (a b x : Obj) (f : x ~> a) (g : x ~> b),
                     (f &&& g) \\o proj2 === g;
    med_unique : forall (a b x : Obj) (f : x ~> a) (g : x ~> b) (h : x ~> (Prod a b)),
                   h \\o proj1 === f ->
                   h \\o proj2 === g ->
                   h === (f &&& g)
  }.

(* **** *)
(* Sets *)
(* **** *)
Instance EquivExt : forall (A B : Set), Equivalence (@eqfun A B) := (* notu *)
  {
    Equivalence_Reflexive := @frefl A B;
    Equivalence_Symmetric := @fsym A B;
    Equivalence_Transitive := @ftrans A B
  }.

Instance EqMor : forall (A B : Set), Setoid :=
  {
    carrier := A -> B;
    eqv := @eqfun B A
  }.
  
Check @Category Set : (Set → Set → Setoid) → Type.
Check EqMor : Set -> Set -> Setoid.
Check @Category Set EqMor : Type.

Program Instance Sets : @Category Set EqMor.
Obligation 3.
Proof.
  rewrite /Sets_obligation_2.
  move=> homab homab' Hhomab hombc hombc' Hhombc.
  move=> x //=.
  rewrite Hhomab.
  rewrite Hhombc.
    by [].
Qed.

(*
Instance Prod : Product prod :=
  {
    proj1 A B := @fst A B;
    proj2 A B := @snd A B ;
    mediating A B X := fun f g x => (f x, g x)
  }.
Proof.
  - by rewrite //=.
       - by rewrite //=.
            - rewrite /commute /= /eqfun.
    move=> A B X f g h H H0 x.
    rewrite -H -H0.
        by apply surjective_pairing.
  Qed.
*)


(* **** *)
(* P,<= *)
(* **** *)
Open Scope coq_nat_scope.
Search "_ <= _".
Check 0 <= 0 : Prop.

Definition eq_le m n (p q : m <= n) := True.
  
Instance EquivGeq : forall m n, Equivalence (@eq_le m n). (* notu *)
Proof.
    by [].
Qed. 
  
Instance EqLe : forall m n, Setoid :=
  {
    carrier := m <= n;
    eqv := @eq_le m n
  }.

Check @Category nat : (nat → nat → Setoid) → Type.
Check EqLe : nat → nat → Setoid.
Check @Category nat EqLe.

Program Instance P_LE : @Category nat EqLe.
Obligation 2.
Proof.
    by apply (@Le.le_trans a b c).
Defined.
Obligation 3.
Proof.
  rewrite /P_LE_obligation_1.
  rewrite /P_LE_obligation_2.
  move=> homab homab' Hhomab hombc hombc' Hhombc.
  by rewrite /eq_le.
Defined.
Obligation 4.
Proof.
  rewrite /P_LE_obligation_1.
  rewrite /P_LE_obligation_2.
  by rewrite /eq_le.
Defined.
Obligation 5.
Proof.
  rewrite /P_LE_obligation_1.
  rewrite /P_LE_obligation_2.
  by rewrite /eq_le.
Defined.

(* END *)
