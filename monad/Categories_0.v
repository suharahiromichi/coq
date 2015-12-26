(* http://www.megacz.com/berkeley/coq-categories/ *)
(* Steve Awodey's book on category theory *)
(******************************************************************************)
(* Chapter 1.3: Categories                                                    *)
(******************************************************************************)
(* これをもとに改変、やっていることは同じ。 *)
(* @suharahiromichi *)


Require Import Morphisms.
Require Import Coq.Setoids.Setoid.

Reserved Notation "x ---> y" (at level 51, left associativity).
Reserved Notation "x \\o y" (at level 51, left associativity).
Reserved Notation "x === y" (at level 71, left associativity).

Definition relation (A : Type) := A -> A -> Prop.

Class Reflexive {A : Type} (R : relation A) :=
  reflexivity : forall x, R x x.

Class Symmetric {A : Type} (R : relation A) :=
  symmetry : forall x y, R x y -> R y x.

Class Transitive {A : Type} (R : relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.

Record Equivalence {A : Type} (R : relation A) : Prop :=
  Build_Equivalence
    {
      Equivalence_Reflexive : Reflexive R;
      Equivalence_Symmetric : Symmetric R;
      Equivalence_Transitive : Transitive R
    }.
  
Generalizable Variables a b c d e.

Class Category (Ob : Type) (Hom : Ob -> Ob -> Type) :=
  {
    hom := Hom where "a ---> b" := (hom a b);
    ob  := Ob;
    id   : forall {a : Ob}, a ---> a;
    comp : forall {a b c : Ob}, a ---> b -> b ---> c -> a ---> c  where "f \\o g" := (comp f g);
    eqv  : forall {a b : Ob}, a ---> b -> a ---> b -> Prop        where "f === g" := (eqv f g);
    eqv_equivalence : forall {a b : Ob}, Equivalence (@eqv a b);
    comp_respects   : forall {a b c : Ob}, Proper (@eqv a b ==> @eqv b c ==> @eqv a c) comp;
    left_identity   : forall `(f : a ---> b), @id a \\o f === f;
    right_identity  : forall `(f : a ---> b), f \\o @id b === f;
    associativity   : forall `(f : a ---> b) `(g : b ---> c) `(h : c ---> d),
                        (f \\o g) \\o h === f \\o (g \\o h)
}.
Coercion ob : Category >-> Sortclass.

Notation "a ---> b"       := (hom a b).
Notation "f === g"        := (eqv f g).
Notation "f \\o g"        := (comp f g).
(* Notation "a ~~{ C }~~> b" := (@hom _ _ C a b). *)


Generalizable Variables Ob Hom.

Add Parametric Relation (Ob:Type)(Hom:Ob->Ob->Type)(C:Category Ob Hom)(a b:Ob) :
  (@hom Ob Hom C a b) (@eqv Ob Hom C a b)
    reflexivity proved by  (@Equivalence_Reflexive  _ _ (@eqv_equivalence Ob Hom C a b))
    symmetry proved by     (@Equivalence_Symmetric  _ _ (@eqv_equivalence Ob Hom C a b))
    transitivity proved by (@Equivalence_Transitive _ _ (@eqv_equivalence Ob Hom C a b))
      as parametric_relation_eqv.

Add Parametric Morphism `(C : Category Ob Hom)(a b c:Ob) : (@comp Ob Hom C a b c)
    with signature (@eqv Ob Hom C a b ==> @eqv Ob Hom C b c ==> @eqv Ob Hom C a c)
      as parametric_morphism_comp.
Proof.
  admit.
Defined.


(*
Class parametric_morphism_comp `(C : Category Ob Hom) (a b c : Ob) :=
  subst :> Proper (@eqv Ob Hom C a b ==> @eqv Ob Hom C b c ==> @eqv Ob Hom C a c) comp.
 *)

Lemma juggle1 : forall `{C:Category} `(f : a ---> b) `(g : b ---> c) `(h : c ---> d) `(k : d ---> e),
                  (((f \\o g) \\o h) \\o k) === (f \\o (g \\o h) \\o k).
Proof.
  intros.
  Check associativity f g h.
  setoid_rewrite <- associativity.
  reflexivity.
Defined.

Lemma juggle2 : forall `{C:Category}`(f:a ---> b)`(g:b ---> c)`(h:c ---> d)`(k:d ---> e),
                  (f \\o (g \\o (h \\o k))) === (f \\o (g \\o h) \\o k).
  intros; repeat setoid_rewrite <- associativity. reflexivity.
Defined.

Lemma juggle3 : forall `{C:Category}`(f:a ---> b)`(g:b ---> c)`(h:c ---> d)`(k:d ---> e),
                  ((f \\o g) \\o (h \\o k)) === (f \\o (g \\o h) \\o k).
  intros; repeat setoid_rewrite <- associativity. reflexivity.
Defined.

(* END *)
