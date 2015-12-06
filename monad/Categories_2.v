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
    id   : forall {a : Obj}, a ~> a;
    comp : forall {a b c : Obj}, a ~> b -> b ~> c -> a ~> c where "f \\o g" := (comp f g);
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

Generalizable Variables Obj Hom.

(*
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
 *)

Instance category_eqv_Equiv `(C : Category Obj) (a b : Obj) :
  Equivalence (@eqv (a ~> b)).
Proof.
  by apply eqv_equivalence.
Qed.

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

(* **** *)
(* Sets *)
(* **** *)

Check @Category Set.
Check (fun (A B : Set) => A -> B) : Set → Set → Set.
Check @Category Set (fun (A B : Set) => A -> B) : Type.

Program Instance Sets : @Category Set (fun (A B : Set) => A -> B).


(* **** *)
(* P,<  *)
(* **** *)

Check @Category nat : (nat → nat → Type) → Type.
Check le : nat → nat → Prop.
Check @Category nat le.

Program Instance P_LE : @Category nat le.
Obligation 2.
Proof.
(*
le_trans : forall n m p : nat, m <= n -> n <= p -> m <= p
 *)
  Check @Le.le_trans a b c.
    by apply (@Le.le_trans a b c).
Defined.
Obligation 3.
Proof.
  rewrite /P_LE_obligation_1.
  rewrite /P_LE_obligation_2.
  Check 
  admit.
Defined.
Obligation 4.
Proof.
  rewrite /P_LE_obligation_1.
  rewrite /P_LE_obligation_2.
  admit.
Defined.
Obligation 5.
Proof.
  rewrite /P_LE_obligation_2.
  admit.
Defined.

(* END *)
