(* TCfM から圏論の定義の部分を抜き出す。 *)
(* "Type Classes for Mathematics in Type Theory" *)

(* Global Generalizable All Variables. *)

(* Set Implicit Arguments. *)

Generalizable Variables O x y.

Require Import Relations.
Require Import Morphisms.                   (* Proper *)

Class Equiv A := equiv : relation A.

Class Arrows (O : Type) : Type := Arrow : O -> O -> Type.

Notation "A == B" := (equiv A B) (at level 55, right associativity).
Notation "A --> B" := (Arrow A B) (at level 55, right associativity).

Class CatId O `{Arrows O} := cat_id : `(x --> x).
Class CatComp O `{Arrows O} :=
  comp : forall {x y z}, (y --> z) -> (x --> y) -> (x --> z).

Notation "A \o B" := (comp A B) (at level 40, left associativity).

Class Setoid A {Ae : Equiv A} : Prop := setoid_eq :> Equivalence (@equiv A Ae).

Class Category (O : Type) `{!Arrows O} `{forall x y : O, Equiv (x --> y)}
      `{!CatId O} `{!CatComp O} : Prop :=
  {
    arrow_equiv :> forall x y, Setoid (x --> y);
    comp_proper :> forall x y z, Proper (equiv ==> equiv ==> equiv) (@comp _ _ _ x y z);
    comp_assoc w x y z (a : w --> x) (b : x --> y) (c : y --> z) :
      c \o (b \o a) = (c \o b) \o a;
    id_l `(a : x --> y) : cat_id _ \o a = a;
    id_r `(a : x --> y) : a \o cat_id _ = a;
  }.


Require Import Omega.
Require Import Coq.Logic.ProofIrrelevance.

(* *********** *)
(* シングルトン *)
(* *********** *)

Definition O0 : Type := unit.
Definition A0 : Arrows O0 := fun (x y : unit) => nat.
Definition E0 (x y : unit) : Equiv (x --> y) := fun (m n : nat) => m = n.
Definition I0 : CatId O0 := fun (_ : unit) => 0.
Definition C0 : CatComp O0 := fun (_ _ _ : unit) (m n : nat) => m + n.

Check Category O0 : Prop.
Check @Category O0 A0 E0 I0 C0 : Prop.
Program Instance SPLUS : @Category O0 A0 E0 I0 C0.
Obligation 1.
Proof.
  unfold Setoid, equiv, E0.
  split.
  + now unfold Reflexive.
  + now unfold Symmetric.
  + unfold Transitive.
    intros x' y' z H1 H2.
    now rewrite H1, H2.
Qed.
Obligation 2.
Proof.
  unfold comp, C0.
  now apply plus_assoc.
Qed.

Check @Arrow unit A0 tt tt : Type.
Check @comp O0 A0 C0 tt tt tt 3 2 : tt --> tt.
Check @cat_id O0 A0 I0 tt : tt --> tt.

(* END *)
