(* http://www.megacz.com/berkeley/coq-categories/ *)
(* Steve Awodey's book on category theory *)
(******************************************************************************)
(* Chapter 1.3: Categories                                                    *)
(***`***************************************************************************)
(* これをもとに改変。Instance ... Proper を使うようにした。 *)
(* @suharahiromichi *)

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

Class Category (Obj : Type) (Hom : Obj -> Obj -> Type) :=
  {
    hom := Hom where "a ~> b" := (hom a b);
    ob  := Obj;
    id   : forall {a : Obj}, a ~> a;
    comp : forall {a b c : Obj}, a ~> b -> b ~> c -> a ~> c where "f \\o g" := (comp f g);
    eqv  : forall {a b : Obj}, a ~> b -> a ~> b -> Prop     where "f === g" := (eqv f g);
    
    eqv_equivalence : forall {a b : Obj}, Equivalence (@eqv a b);
    comp_respects   : forall {a b c : Obj}, Proper (@eqv a b ==> @eqv b c ==> @eqv a c) comp;
    
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

Generalizable Variables Obj Hom.

 (* eqv が、Reflexive と Symmetric と Transitive とを満たす。 *)
 Instance category_eqv_Equiv `(C : Category Obj Hom) (a b : Obj) :
  Equivalence (@eqv Obj Hom C a b).
Proof.
  by apply eqv_equivalence.
Qed.

(* comp は eqv について固有関数である。 *)
Instance category_comp_Proper `(C : Category Obj Hom) (a b c : Obj) :
  Proper (@eqv Obj Hom C a b ==> @eqv Obj Hom C b c ==> @eqv Obj Hom C a c) (comp).
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

(* END *)
