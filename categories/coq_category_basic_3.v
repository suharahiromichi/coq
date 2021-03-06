(* comp := fun f g x => f (g x) と 定義する版 *)
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

半順序集合の圏
対象の型  nat
対象の例  3,4
射の型    Hom := ∀m n : nat, m ≦ n
射の型    Hom 3 4    (= 3 ≦ 4)
射の例    le3_4

しりとりの圏
対象の型  Hira
対象の例  こ,ぶ,た
射の型    (Inductive な定義)
射の例    こ ぶ た

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
Require Import Coq.Logic.ProofIrrelevance.
(* Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2. *)

Set Implicit Arguments.

Generalizable Variables Obj.

Class Category `(Hom : Obj -> Obj -> Set) : Type :=
  {
    Hom := Hom;
    Obj := Obj;
    id              : forall {A : Obj}, Hom A A;
    comp            : forall {A B C : Obj}, Hom B C -> Hom A B -> Hom A C; (* *** *)
    left_identity   : forall {A B : Obj} {f : Hom A B}, comp id f = f;
    right_identity  : forall {A B : Obj} {f : Hom A B}, comp f id = f;
    associativity   : forall {A B C D : Obj} {f : Hom C D} {g : Hom B C} {h : Hom A B},
        comp f (comp g h) = comp (comp f g) h
  }.

Notation "A ~> B" := (Hom A B) (at level 51, left associativity).
Notation "f \o g" := (comp f g) (at level 51, left associativity).

(* *********** *)
(* シングルトン *)
(* *********** *)
Definition Hom0 (A B : unit) : Set := nat.
Program Instance SINGLETON : @Category unit Hom0 :=
  {|
    id _ := 0;
    comp _ _ _ := fun m n => m + n
  |}.
Obligation 3.
Proof.
  now apply plus_assoc.
Qed.

(* 例 *)
Check Hom : unit -> unit -> Set.
Check comp 2 3 : Hom tt tt.
Compute comp 2 3.
Check 2 \o 3 : tt ~> tt.

(* ******** *)
(* 集合の圏 *)
(* ******** *)
Definition Hom1 (A B : Set) : Set := A -> B.
Program Instance SETS : @Category Set Hom1 :=
  {|
    id _ := fun x => x;
    comp _ _ _ := fun f g x => f (g x)      (* *** *)
  |}.

(* 例 *)
Check Hom : Set -> Set -> Set.
Check comp (plus 2) (plus 3) : Hom nat nat.
Compute comp (plus 2) (plus 3).
Check (plus 2) \o (plus 3) : nat ~> nat.

(* ************* *)
(* 半順序集合の圏 *)
(* ************* *)
Definition Hom2 (m n : nat) : Set := m <= n.
Definition id2 (n : nat) : Hom2 n n.
Proof.
  unfold Hom2. easy.                        (* omega でなく *)
Defined.
Definition comp2 {m n p} H2 H1 := le_trans m n p H1 H2.

Program Instance NAT : @Category nat Hom2 :=
  {|
    id := id2;
    comp nat  _ _ := comp2
  |}.
Obligation 1.
Proof.
  unfold Hom2 in *.
  apply proof_irrelevance.
Qed.
Obligation 2.
Proof.
  unfold Hom2 in *.
  apply proof_irrelevance.
Qed.
Obligation 3.
Proof.
  unfold Hom2 in *.
  apply proof_irrelevance.
Qed.

(* 例 *)
Definition le34 : Hom 3 4. Proof. unfold Hom, Hom2. omega. Defined.
Definition le45 : Hom 4 5. Proof. unfold Hom, Hom2. omega. Defined.
Check comp le45 le34 : Hom 3 5.
Compute comp le45 le34.
Check le45 \o le34 : 3 ~> 5.

(* *********** *)
(* しりとりの圏 *)
(* *********** *)
(* http://yosh.hateblo.jp/entry/20090425/p1 *)
(* comp の引数の順番を関数とおなじにしている。 *)
Inductive Hira : Set := こ | ぶ | た | ぬ | き | つ | ね.
Inductive Hom3 : Hira -> Hira -> Set :=
  | single : forall A, Hom3 A A
  | cons : forall {A' B : Hira} (A : Hira) (tl : Hom3 A' B), Hom3 A B.

Definition comp3 {A B C : Hira} (f : Hom3 B C) (g : Hom3 A B) : Hom3 A C.
Proof.
  intros.
  induction g.
  + easy.
  + Check (cons A (IHg f)).
    apply (cons A (IHg f)).
Defined.

Program Instance SIRI : @Category Hira Hom3 :=
  {|
    id := single;
    comp _ _ _ := comp3
  |}.
Obligation 1.
  induction f.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHf.
    reflexivity.
Qed.
Obligation 3.
Proof.
  induction h.
  + easy.
  + simpl.
    now rewrite IHh.
Qed.

(* 例 *)
Definition こぶた := cons こ (cons ぶ (single た)) : Hom こ た.
Definition たぬき := cons た (cons ぬ (single き)) : Hom た き.
Check comp たぬき こぶた : Hom こ き.
Compute comp たぬき こぶた.          (* こ ぶ た ぬ き : Home こ き *)
Check たぬき \o こぶた : こ ~> き.

(* END *)
