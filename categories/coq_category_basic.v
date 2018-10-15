(**
シングルトン
対象の型  unit
対象の例  tt（のみ）
射の型    Hom := ∀a b : unit, nat
射の型    Hom tt tt  (= nat)
射の例    1, 2

集合の圏
対象の型  Set
対象の例  nat（のみ）
射の型    Hom := ∀A B : Set, A -> B
射の型    Hom nat nat  (= nat -> nat)
射の例    plus 1, plus 2

LEの圏
対象の型  nat
対象の例  3,4
射の型    Hom := ∀m n : nat, m ≦ n
射の型    Hom 3 4    (= 3 ≦ 4)
射の例    le3_4

しりとりの圏
対象の型  Hira
対象の例  こ,た
射の型    (Inductive な定義)
射の例    siri こ た

型の圏
対象の型  Type
対象の例  nat
射の型    Hom := ∀A B : Type, A -> B
射の型    Hom nat nat  (= nat -> nat)
射の例    plus 1, plus 2  (項)

論理式の圏
対象の型  Prop
対象の例  1=2,2=1
射の型    Hom := ∀A B : Prop, A -> B
射の型    Hom (1=2) (2=1)
射の例    1=2 -> 2=1    (演繹、証明図）
*)

Require Import Omega.
Set Implicit Arguments.

(* Cat0 シングルトン *)
Definition Hom0 (A B : unit) : Set := nat.
Check Hom0 : unit -> unit -> Set.
Check 1 : Hom0 tt tt.
Check 2 : Hom0 tt tt.
Definition comp0 (m n : Hom0 tt tt) : Hom0 tt tt := m + n.
Check comp0.
Check comp0 1 2 : Hom0 tt tt.
Compute comp0 1 2.                          (* 3 *)

(* 恒等射 identity *)
Definition id0 : Hom0 tt tt := 0.

(* 単位元律 unit law 01 *)
Theorem unit0_l : forall (f : Hom0 tt tt), comp0 id0 f = f.
Proof.
  intros.
  reflexivity.
Qed.
(*
Theorem unit0_l : forall (n : nat), comp0 id0 n = n.
Proof.
  intros.
  reflexivity.
Qed.
 *)
  
(* 単位元律 unit law 02 *)
Theorem unit0_r : forall (f : Hom0 tt tt), comp0 f id0 = f.
Proof.
  intros.
  unfold id0, comp0.
  Search _ (_ + 0 = _).
  apply Nat.add_0_r.
Qed.
(*
Theorem unit0_r : forall (n : nat), comp0 n id0 = n.
Proof.
  intros.
  unfold id0, comp0.
  Search _ (_ + 0 = _).
  apply Nat.add_0_r.
Qed.
 *)
  
(* 結合律 associative low *)
Theorem assoc0 : forall (f : Hom0 tt tt) (g : Hom0 tt tt) (h : Hom0 tt tt),
    comp0 f (comp0 g h) = comp0 (comp0 f g) h.
Proof.
 unfold id0, comp0.
 Search _ (_ + _ + _ = _).
 apply plus_assoc.
Qed.
(*
Theorem assoc0 : forall m n p,
    comp0 m (comp0 n p) = comp0 (comp0 m n) p.
Proof.
 intros.
 unfold id0, comp0.
 Search _ (_ + _ + _ = _).
 apply plus_assoc.
Qed.
*)

(* Cat1 集合の圏 *)
Definition Hom1 (A B : Set) : Set := A -> B.
Check Hom1 : Set -> Set -> Set.
Check plus 1 : Hom1 nat nat.
Check plus 2 : Hom1 nat nat.
Definition comp1 {A B C : Set} (f : Hom1 A B) (g : Hom1 B C) : Hom1 A C
  := fun x => g (f x).
Check comp1 (plus 1) (plus 2) : Hom1 nat nat.
Compute comp1 (plus 1) (plus 2).            (* fun x : x + 3 *)


(* 恒等射 identity *)
Definition id1 : Hom1 nat nat := fun x => x. (* plus 0 *)

(* 単位元律 unit law 01 *)

Theorem unit1_l : forall (f : Hom1 nat nat), comp1 f id1 = f.
Proof.
  intros.
  reflexivity.
Qed.
(* Theorem unit1_l : forall (n : nat), comp1 id1 (plus n) = plus n. *)

(* 単位元律 unit law 02 *)
Theorem unit1_r : forall (f : Hom1 nat nat), comp1 f id1 = f.
Proof.
  intros.
  reflexivity.
Qed.
(* Theorem unit1_r : forall (n : nat), comp1 (plus n) id1 = plus n. *)

(* 結合律 associative low *)
Theorem assoc1 : forall (f : Hom1 nat nat) (g : Hom1 nat nat) (h : Hom1 nat nat),
    comp1 f (comp1 g h) = comp1 (comp1 f g) h.
Proof.
  intros.
  reflexivity.
Qed.
(*
Theorem assoc1 : forall m n p,
    comp1 (plus m) (comp1 (plus n) (plus p)) =
    comp1 (comp1 (plus m) (plus n)) (plus p).
*)

(* 関手 *)
Definition F (n : Hom0 tt tt) : Hom1 nat nat := plus n.
Check comp1 (F 1) (F 2) : Hom1 nat nat.
Compute comp1 (F 1) (F 2).                  (* fun x => x + 3 *)

Definition G (f : Hom1 nat nat) : Hom0 tt tt := f 0.
Check comp0 (G (plus 1)) (G (plus 2)) : Hom0 tt tt.
Compute comp0 (G (plus 1)) (G (plus 2)).    (* 3 *)

(* Cat2 半順序集合の圏 *)
Definition Hom2 (m n : nat) : Set := m <= n.
Check Hom2 : nat -> nat -> Set.
Definition le34 : Hom2 3 4. Proof. unfold Hom2. omega. Defined.
Definition le45 : Hom2 4 5. Proof. unfold Hom2. omega. Defined.
Definition comp2 {m n p} H1 H2 := le_trans m n p H1 H2.
Check comp2 le34 le45 : Hom2 3 5.
Compute comp2 le34 le45.
(* Aw_1_3_Categories.v の定義だとcompが異なるのでirrelevanceが要らない。 *)

Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.
Definition le35 : Hom2 3 5. Proof. unfold Hom2. omega. Defined.
Goal comp2 le34 le45 = le35.                (* irrelevance が必要 *)
Proof.
  apply proof_irrelevance.
Qed.

(* 恒等射 identity *)
Definition id2 (n : nat) : Hom2 n n.
Proof.
  unfold Hom2. easy.                        (* omega でなく *)
Defined.

(* 単位元律 unit law 01 *)
Theorem unit2_l : forall (m n : nat) (f : Hom2 m n),
    comp2 (id2 m) f = f.                    (* irrelevance が必要 *)
Proof.
  intros.
  apply proof_irrelevance.
Qed.

(* 単位元律 unit law 02 *)
Theorem unit2_r : forall (m n : nat) (f : Hom2 m n),
    comp2 f (id2 n) = f.                    (* irrelevance が必要 *)
Proof.
  intros.
  apply proof_irrelevance.
Qed.

(* 結合律 associative low *)
Theorem assoc2 : forall (m n p l : nat) (f : Hom2 m n) (g : Hom2 n p) (h : Hom2 p l),
    comp2 f (comp2 g h) = comp2 (comp2 f g) h. (* irrelevance が必要 *)
Proof.
  intros.
  apply proof_irrelevance.
Qed.

(* Cat3 しりとりの圏 *)
Inductive Hira : Set := こ | ぶ | た | ぬ | き | つ | ね.
Inductive Hom3 : Hira -> Hira -> Set :=
  | single : forall A, Hom3 A A
  | cons : forall {A' B : Hira} (A : Hira) (tl : Hom3 A' B), Hom3 A B.
(*
Inductive Hom3 : Hira -> Hira -> Set := siri : forall (a b : Hira), Hom3 a b.
*)
Check Hom3 : Hira -> Hira -> Set.
Definition こぶた := cons こ (cons ぶ (single た)) : Hom3 こ た.
Definition たぬき := cons た (cons ぬ (single き)) : Hom3 た き.

Definition comp3 {A B C : Hira} (f : Hom3 A B) (g : Hom3 B C) : Hom3 A C.
Proof.
  intros.
  induction f.
  + easy.
  + Check (cons A (IHf g)).
    apply (cons A (IHf g)).
Defined.

Check comp3 こぶた たぬき : Hom3 こ き.
Compute comp3 こぶた たぬき.        (* こ ぶ た ぬ き : Home3 こ き *)

(* 恒等射 identity *)
Definition id3 A : Hom3 A A := single A.

(* 単位元律 unit law 01 *)
Theorem unit3_l : forall (A B : Hira) (f : Hom3 A B), comp3 (id3 A) f = f.
Proof.
  intros.
  now simpl.
Qed.

(* 単位元律 unit law 02 *)
Theorem unit3_r : forall (A B : Hira) (f : Hom3 A B), comp3 f (id3 B) = f.
Proof.
  intros.
  induction f.
  + easy.
  + simpl.
    now rewrite IHf.
Qed.

(* 結合律 associative low *)
Theorem assoc3 : forall (A B C D : Hira) (f : Hom3 A B) (g : Hom3 B C) (h : Hom3 C D),
    comp3 f (comp3 g h) = comp3 (comp3 f g) h.
Proof.
  intros.
  induction f.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHf.
    reflexivity.
Qed.

(* END *)

Generalizable Variables Obj.

(*
Class Category1 `(Hom : Obj -> Obj -> Set) : Type :=
  {
  }.
Program Instance SINGLETON1 : Category1 Hom0. (* unit *)
Program Instance SETS1      : Category1 Hom1. (* Set *)
Program Instance NAT1       : Category1 Hom2. (* nat *)
Program Instance SIRI1      : Category1 Hom3. (* Hira *)

Class Category2 `(Hom : Obj -> Obj -> Set) : Type :=
  {
    comp22 : forall {A B C : Obj}, Hom A B -> Hom B C -> Hom A C
  }.

Program Instance SINGLETON2 : Category2 Hom0. (* unit *)

Program Instance SETS2      : Category2 Hom1. (* Set *)
Obligation 1.
Proof.
  Check @comp1 A B C.
  now apply (@comp1 A B C).
Defined.

Program Instance NAT2       : Category2 Hom2. (* nat *)
Obligation 1.
Proof.
  unfold Hom2 in *.
  eapply comp2.
  - now apply H.
  - now apply H0.
Defined.

Program Instance SIRI2      : Category2 Hom3. (* Hira *)
Obligation 1.
Proof.
  eapply comp3.
  - now apply H.
  - now apply H0.
Defined.

Class Category3 `(Hom : Obj -> Obj -> Set) : Type :=
  {
    id33  : forall {A : Obj}, Hom A A
  }.

Program Instance SINGLETON3 : Category3 Hom0. (* unit *)
Obligation 1.
Proof.
  Check id0.
  now apply id0.
Defined.

Program Instance SETS3      : Category3 Hom1. (* Set *)
Obligation 1.
Proof.
  Check id1.
Admitted.

Program Instance NAT3       : Category3 Hom2. (* nat *)
Obligation 1.
Proof.
  Check id2.
  now eapply id2.
Defined.

Program Instance SIRI3      : Category3 Hom3. (* Hira *)
Obligation 1.
Proof.
  now eapply id3.
Qed.
*)

Class Category `(Hom : Obj -> Obj -> Set) : Type :=
  {
    id   : forall {A : Obj}, Hom A A;
    comp : forall {A B C : Obj}, Hom A B -> Hom B C -> Hom A C;
    left_identity   : forall {A B : Obj} {f : Hom A B}, comp id f = f;
    right_identity  : forall {A B : Obj} {f : Hom A B}, comp f id = f;
    associativity   : forall {A B C D : Obj} {f : Hom A B} {g : Hom B C} {h : Hom C D},
        comp f (comp g h) = comp (comp f g) h
  }.

Program Instance SINGLETON : Category Hom0 := (* unit *)
  {|
    comp _ _ _ := comp0
  |}.
Obligation 1.
Proof.
  Check id0.
  now apply id0.
Defined.
Obligation 4.
Proof.
  unfold id0, comp0.
  apply plus_assoc.
Qed.


Program Instance SETS      : Category Hom1 := (* Set *)
  {|
    id nat     := fun x => x;
    comp _ _ _ := comp1
  |}.

Program Instance NAT       : Category Hom2. (* nat *)
Obligation 1.
Proof.
  Check id2.
  now apply id2.
Defined.
Obligation 2.
  unfold Hom2 in *.
  eapply comp2.
  - now apply H.
  - now apply H0.
Defined.
Obligation 3.
Proof.
  unfold NAT_obligation_2.
  unfold NAT_obligation_1.
  unfold comp2.
  unfold id2.                               (* omega でなく easy で解くこと。 *)
  unfold Hom2 in *.
  apply proof_irrelevance.
Qed.
Obligation 4.
  unfold NAT_obligation_2.
  unfold NAT_obligation_1.
  unfold comp2.
  unfold id2.                               (* omega でなく easy で解くこと。 *)
  unfold Hom2 in *.
  apply proof_irrelevance.
Qed.
Obligation 5.
  unfold NAT_obligation_2.
  unfold comp2.
  unfold id2.                               (* omega でなく easy で解くこと。 *)
  unfold Hom2 in *.
  apply proof_irrelevance.
Qed.

Program Instance SIRI      : Category Hom3. (* Hira *)
Obligation 1.
Proof.
  now eapply id3.
Defined.
Obligation 2.
Proof.
  eapply comp3.
  - now apply H.
  - now apply H0.
Defined.
Obligation 4.
  unfold SIRI_obligation_2.
  unfold SIRI_obligation_1.
  induction f.
  + easy.
  + simpl.
    now rewrite IHf.
Qed.
Obligation 5.
  unfold SIRI_obligation_2.
  unfold SIRI_obligation_1.
  intros.
  induction f.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHf.
    reflexivity.
Qed.

(* END *)
