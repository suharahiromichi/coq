(* TCfM から圏論の定義の部分を抜き出す。 *)
(* "Type Classes for Mathematics in Type Theory" *)

(* Global Generalizable All Variables. *)

(* Set Implicit Arguments. *)

Require Import Relations.
Require Import Morphisms.                   (* Proper *)

Require Import Omega.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Section Category_Class.
  Generalizable Variables O x y.
  
  Class Arrows (O : Type) : Type := arrow : O -> O -> Type.
  Class Equiv A := equiv : relation A.
  
  Notation "A == B" := (equiv A B) (at level 55, right associativity).
  Notation "A --> B" := (arrow A B) (at level 55, right associativity).
  
  Class CatId O `{Arrows O} := cat_id : `(x --> x).
  Class CatComp O `{Arrows O} :=
    comp : forall {x y z}, (y --> z) -> (x --> y) -> (x --> z).
  
  Notation "A \o B" := (comp A B) (at level 40, left associativity).
  
  Class Setoid A {Ae : Equiv A} : Prop :=
    setoid_eq :> Equivalence (@equiv A Ae).
  (* これは、Operational Class である。
     Prop. Class にした場合は、unfold Setoid を split に変える。 *)
  
  Section setoid_morphisms.
  Context {A B} {Ae : Equiv A} {Be : Equiv B} (f : A -> B).    
    Class Setoid_Morphism :=
      {
        setoidmor_a : Setoid A;
        setoidmor_b : Setoid B;
        sm_proper :> Proper (equiv ==> equiv) f
      }. 
  End setoid_morphisms.
  
  Class Category (O : Type)
        `{!Arrows O}
        `{forall x y : O, Equiv (x --> y)}
        `{!CatId O}
        `{!CatComp O} : Prop :=
    {
      arrow_equiv :> forall x y, Setoid (x --> y);
      comp_proper :> forall x y z,
          Proper (equiv ==> equiv ==> equiv) (@comp _ _ _ x y z);
      comp_assoc w x y z (a : w --> x) (b : x --> y) (c : y --> z) :
        c \o (b \o a) = (c \o b) \o a;
      id_l `(a : x --> y) : cat_id _ \o a = a;
      id_r `(a : x --> y) : a \o cat_id _ = a;
    }.
End Category_Class.

Notation "A == B" := (equiv A B) (at level 55, right associativity).
Notation "A --> B" := (arrow A B) (at level 55, right associativity).
Notation "A \o B" := (comp A B) (at level 40, left associativity).

(* *********** *)
(* シングルトン *)
(* *********** *)

Definition O0 : Type := unit.
Instance A0 : Arrows O0 := fun (x y : O0) => nat.
Instance E0 (x y : O0) : Equiv (A0 x y) := fun (m n : nat) => m = n.
Instance I0 : CatId O0 := fun (_ : O0) => 0.
Instance C0 : CatComp O0 := fun (_ _ _ : O0) (m n : nat) => m + n.

Check Category O0 : Prop.
Check @Category O0 A0 E0 I0 C0 : Prop.
Program Instance SPLUS : @Category O0 A0 E0 I0 C0.
Obligation 1.                               (* Setoid (x --> y) *)
Proof.
  unfold Setoid.                            (* Equivalence equiv *)
  unfold equiv.                             (* Equivalence (E0 x y) *)
  unfold E0.                                (* Equivalence (fun m n : nat => m = n) *)
  split.
  + now unfold Reflexive.
  + now unfold Symmetric.
  + unfold Transitive.
    intros x' y' z' H1 H2.
    now rewrite H1, H2.
Qed.
Obligation 2.
Proof.
  unfold comp, C0.
  now apply plus_assoc.
Qed.

(* 例 *)
Check @cat_id O0 A0 I0 tt : tt --> tt.
Compute @cat_id O0 A0 I0 tt.                (* 0 *)
Check @comp O0 A0 C0 tt tt tt 3 2 : tt --> tt.
Compute @comp O0 A0 C0 tt tt tt 3 2.        (* 5 *)


(* ******** *)
(* 集合の圏 *)
(* ******** *)

Definition O1 : Type := Set.
Instance A1 : Arrows O1 := fun (x y : O1) => x -> y.
Instance E1 (x y : O1) : Equiv (A1 x y) := (* x -> y *)
  fun (f g : A1 x y) => forall (a : x), f a = g a.
(*
Instance E1 (x y : O1) : Equiv (A1 x y) := (* x -> y *)
  fun (f g : A1 x y) => f = g.
*)
Instance I1 : CatId O1 := fun (a : O1) (x : a) => x.
Instance C1 : CatComp O1 :=
  fun (x y z : O1) (f : A1 y z) (g : A1 x y) (a : x) => f (g a).

Check Category O1 : Prop.
Check @Category O1 A1 E1 I1 C1 : Prop.
Program Instance SETS : @Category O1 A1 E1 I1 C1.
Obligation 1.
Proof.
  unfold Setoid, equiv, E1.
  split.
  + now unfold Reflexive.
  + now unfold Symmetric.
  + unfold Transitive.
    intros x' y' z' H1 H2 a.
    rewrite H1.
    rewrite <- H2.
    easy.
Qed.
Obligation 2.
Proof.
  unfold equiv, E1, comp, C1.
  intros yz yz' H1 xy xy' H2 a.
  rewrite H2.
  rewrite H1.
  easy.
Qed.

(* 例 *)
Check @cat_id O1 A1 I1 nat : nat --> nat.
Compute @cat_id O1 A1 I1 nat.               (* id *)
Check @comp O1 A1 C1 nat nat nat (plus 3) (plus 2) : nat --> nat.
Compute @comp O1 A1 C1 nat nat nat (plus 3) (plus 2). (* plus 5 *)


(* ************* *)
(* 半順序集合の圏 *)
(* ************* *)
Definition O2 : Type := nat.
Instance A2 : Arrows O2 := fun (x y : O2) => x <= y.
Instance E2 (x y : O2) : Equiv (A2 x y) := (* x <= y *)
  fun (H1 H2 : A2 x y) => H1 = H2.
Instance I2 : CatId O2 := le_n.
Instance C2 : CatComp O2 :=
  fun (x y z : O2) H1 H2 => le_trans x y z H2 H1.

Check @Category O2 A2 E2 I2 C2 : Prop.
Program Instance LE : @Category O2 A2 E2 I2 C2.
Obligation 1.
  unfold Setoid, equiv, E2.
  split.
  + now unfold Reflexive.
  + now unfold Symmetric.
  + unfold Transitive.
    intros x' y' z' H1 H2.
    now rewrite H1, H2.
Qed.
Obligation 2.
Proof.
  unfold comp, C2.
  unfold arrow, A2 in *.
  Check proof_irrelevance.
  now apply proof_irrelevance.
Qed.
Obligation 3.
  unfold comp, C2.
  unfold arrow, A2 in *.
  now apply proof_irrelevance.
Qed.
Obligation 4.
  unfold comp, C2.
  unfold arrow, A2 in *.
  now apply proof_irrelevance.
Qed.

(* 例 *)
Definition le33 : 3 <= 3. Proof. easy. Defined.
Definition le34 : 3 <= 4. Proof. omega. Defined.
Definition le45 : 4 <= 5. Proof. omega. Defined.

Check @cat_id O2 A2 I2 2  : 2 --> 2.
Compute @cat_id O2 A2 I2 2.                 (* le_n 2 *)
Check @comp O2 A2 C2 3 4 5 le45 le34 : 3 --> 5.
Compute @comp O2 A2 C2 3 4 5 le45 le34.     (* *** *)


(* *********** *)
(* しりとりの圏 *)
(* *********** *)
Inductive O3 : Type := こ | ぶ | た | ぬ | き | つ | ね.
Inductive A3 : Arrows O3 :=
  | single : forall A, A3 A A
  | cons : forall {A' B : O3} (A : O3) (tl : A3 A' B), A3 A B.

Check cons こ (cons ぶ (single た)) : A3 こ た.
Goal cons こ (cons ぶ (single た)) = cons こ (cons ぶ (single た)).
Proof. reflexivity. Qed.                    (* 普通に = が成り立つ。 *)

Instance E3 (x y : O3) : Equiv (A3 x y) :=
  fun (s t : A3 x y) => s = t.
Definition I3 : CatId O3 := single.

Definition c3 (x y z : O3) (s : A3 x y) (t : A3 y z) : A3 x z. (* CatComp O3. *)
  induction s.
  + easy.
  + now apply (cons A (IHs t)).
Defined.
Definition C3 : CatComp O3 :=
  fun (x y z : O3) (s : A3 y z) (t : A3 x y) => c3 x y z t s.

Check @Category O3 A3 E3 I3 C3 : Prop.
Program Instance SIRI : @Category O3 A3 E3 I3 C3.
Obligation 1.
  unfold Setoid, equiv, E3.
  split.
  + now unfold Reflexive.
  + now unfold Symmetric.
  + unfold Transitive.
    intros x' y' z' H1 H2.
    now rewrite H1, H2.
Qed.
Obligation 2.
Proof.
  unfold comp, C3.
  induction a.
  - now simpl.
  - simpl.
    now rewrite IHa.
Qed.
Obligation 3.
Proof.
  unfold comp, C3.
  induction a.
  - now simpl.
  - simpl.
    now rewrite IHa.
Qed.

(* 例 *)
Definition ko := single こ.
Definition kobuta := cons こ (cons ぶ (single た)).
Definition tanuki := cons た (cons ぬ (single き)).

Check @cat_id O3 A3 I3 こ : こ --> こ.
Compute @cat_id O3 A3 I3 こ.                   (* single こ *)
Check @comp O3 A3 C3 こ た き tanuki kobuta.   (* こ --> き *)
Compute @comp O3 A3 C3 こ た き tanuki kobuta. (* こ ぶ た ぬ き *)

(* 始対象 *)
Section initiality.
  Generalizable Variables X.
  Context `{Category X}.
  
  Class InitialArrow (x : X) : Type := initial_arrow: forall y, x --> y.

  Class Initial (x : X) `{InitialArrow x}: Prop :=
    initial_arrow_unique : forall y f', initial_arrow y = f'.
End initiality.

Program Definition IA0 (x : O0) : @InitialArrow O0 A0 x := fun (y : O0) => _.
Obligation 1.
Admitted.

Program Instance ISNGL : @Initial O0 A0 tt (IA0 tt).
Obligation 1.
Proof.
  unfold initial_arrow, IA0.
  Admitted.

(* 関手 *)

Section functor_class.
  Generalizable Variables C D x y z a.
  
  Context `{Category C} `{Category D} (M : C -> D).
  
  Class Fmap: Type := fmap : forall {v w : C}, (v --> w) -> (M v --> M w).
  
  Class Functor `(Fmap) : Prop :=
    {
      functor_from : Category C;
      functor_to : Category D;
      functor_morphism :> forall a b : C, Setoid_Morphism (@fmap _ a b);
      preserves_id : `(fmap (cat_id _ : a --> a) = cat_id _);
      preserves_comp `(f : y --> z) `(g : x --> y) : fmap (f \o g) = fmap f \o fmap g
    }.
End functor_class.

Definition M01 (a : unit) : O1 := nat.

Check @Fmap.
Check @Fmap O0 A0 O1 A1 M01 : Type.
Check Fmap M01 : Type.

Definition f01 (x y : O0) (n : nat) := fun (x : nat) => x + n.
Definition F01 : @Fmap O0 A0 O1 A1 M01 := f01.

Check @Functor O0 A0 E0 I0 C0 O1 A1 E1 I1 C1 M01 F01.
Check Functor M01 F01.
Program Instance FUN01 : Functor M01 F01.
Obligation 1.
Proof.
  split.
  - split.                                  (* Setoid (a --> b) *)
    + unfold Reflexive.
      now unfold equiv, E0.
    + unfold Symmetric.
      now unfold equiv, E0.
    + unfold Transitive.
      unfold equiv, E0.
      intros.
      now subst.
  - split.                                  (* Setoid (M a --> M b) *)
    + unfold Reflexive.
      now unfold equiv, E1.
    + unfold Symmetric.
      now unfold equiv, E1.
    + unfold Transitive.
      unfold equiv, E1.
      intros.
      erewrite H.
      erewrite <- H0.
      easy.
  - intro x.
    intros y H.
    unfold equiv, E0 in H.
    rewrite H.
    easy.
Qed.

Check Fmap M01.
Check F01.
Check @fmap O0 A0 O1 A1 M01 F01 tt tt : tt --> tt -> nat --> nat.
Check @fmap O0 A0 O1 A1 M01 F01 tt tt   1         :  nat --> nat.
Check plus 1                                      : nat --> nat.

Goal @fmap O0 A0 O1 A1 M01 F01 tt tt   1 = fun x => x + 1.
Proof.
  unfold fmap, M01, F01, f01.
  easy.
Qed.

(* END *)
