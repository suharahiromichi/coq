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
Definition E0 (x y : O0) : Equiv (x --> y) := fun (m n : nat) => m = n.
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


(* ******** *)
(* 集合の圏 *)
(* ******** *)
Definition O1 : Type := Set.
Definition A1 : Arrows O1 := fun (x y : Set) => x -> y.
Program Instance E1 (x y : O1) : Equiv (x -> y).
Obligation 1.
Admitted.
(*
Definition E1 (x y : O1) : Equiv (x --> y) := fun (f g : x -> y) (a : x) => f a = g a.
*)
Definition I1 : CatId O1 := fun (a : O1) (x : a) => x.
Definition C1 : CatComp O1 := fun (x y z : Set) (f : y -> z) (g : x -> y) (a : x) =>
                                f (g a).

Check Category O1 : Prop.
Check @Category O1 A1 E1 I1 C1 : Prop.
Program Instance SETS : @Category O1 A1 E1 I1 C1.
Obligation 1.
Admitted.
Obligation 2.
Admitted.

(* ************* *)
(* 半順序集合の圏 *)
(* ************* *)
Definition O2 : Type := nat.
Definition A2 : Arrows O2 := fun (m n : nat) => m <= n.
Program Instance E2 (x y : O2) : Equiv (x <= y).
Obligation 1.
Proof.
Admitted.
(*
Definition E2 (x y : O2) : Equiv (x --> y) := fun (f g : x --> y) => f = g.
*)

Compute @CatId O2 A2.                       (* forall x : nat, x <= x *)
Lemma test : forall x : nat, x <= x.
Admitted.
Check test : CatId O2.
Definition I2 := test.
Definition C2 : CatComp O2 := fun (m n p : nat) H1 H2 => le_trans m n p H2 H1.

Check @Category O2 A2 E2 I2 C2 : Prop.
Program Instance LE : @Category O2 A2 E2 I2 C2.
Obligation 1.
Admitted.
Obligation 2.
Admitted.


(* *********** *)
(* しりとりの圏 *)
(* *********** *)
Inductive O3 : Type := こ | ぶ | た | ぬ | き | つ | ね.
Inductive A3 : Arrows O3 :=
  | single : forall A, A3 A A
  | cons : forall {A' B : O3} (A : O3) (tl : A3 A' B), A3 A B.

Program Instance E3 (x y : O3) : Equiv (A3 x y).
Obligation 1.
Admitted.
(*
Definition E3 (x y : O3) : Equiv (x --> y) := fun (f g : A3) => f = g.
 *)

Definition I3 : CatId O3 := single.
(*
Definition C3 (A B C : O3) (f : A --> B) (g : B --> C) : A --> C. (* CatComp O3. *)
 *)


(* END *)
