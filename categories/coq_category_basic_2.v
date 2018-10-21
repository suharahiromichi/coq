(* comp := fun f g x => g (f x) と 定義する版 *)
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
    comp            : forall {A B C : Obj}, Hom A B -> Hom B C -> Hom A C;
    left_identity   : forall {A B : Obj} {f : Hom A B}, comp id f = f;
    right_identity  : forall {A B : Obj} {f : Hom A B}, comp f id = f;
    associativity   : forall {A B C D : Obj} {f : Hom A B} {g : Hom B C} {h : Hom C D},
        comp f (comp g h) = comp (comp f g) h
  }.

Notation "A ~{ Cat }~> B" := (@Hom _ _ Cat A B) (at level 51, left associativity).
Notation "A ~> B" := (Hom A B) (at level 51, left associativity).
Notation "f \o g" := (comp g f) (at level 51, left associativity).
Notation "f \{ Cat }o g" := (@comp _ _ Cat _ _ _ g f) (at level 51, left associativity).
Notation "f \; g" := (comp f g) (at level 51, left associativity).
Notation "f \{ Cat }; g" := (@comp _ _ Cat _ _ _ f g) (at level 51, left associativity).

(* *********** *)
(* シングルトン *)
(* *********** *)
Definition Hom0 (A B : unit) : Set := nat.
Program Instance SPLUS : @Category unit Hom0 :=
  {|
    id _ := 0;
    comp _ _ _:= fun m n => n + m           (* 関手が成り立つように (n + m) + x *)
  |}.
Obligation 3.
Proof.
  now apply plus_assoc_reverse.
Qed.

Program Instance SMULT : @Category unit Hom0 :=
  {|
    id _ := 1;
    comp _ _ _:= fun m n => n * m
  |}.
Obligation 1.
Proof.
  now apply Nat.mul_1_r.
Qed.
Obligation 3.
Proof.
  now apply mult_assoc_reverse.
Qed.

(* 例 *)
Check Hom : unit -> unit -> Set.
Check comp 2 3 : Hom tt tt.
Check 2 \; 3 : tt ~> tt.
Check 2 \{SPLUS}; 3 : tt ~{SPLUS}~> tt.
Check 2 \{SMULT}; 3 : tt ~{SMULT}~> tt.
Compute (3 \{SPLUS}; 2).                    (* 3 + 2 = 5 *)
Compute (3 \{SMULT}; 2).                    (* 3 * 2 = 6 *)


(* ******** *)
(* 集合の圏 *)
(* ******** *)
Definition Hom1 (A B : Set) : Set := A -> B.
Program Instance SETS : @Category Set Hom1 :=
  {|
    id _ := fun x => x;
    comp _ _ _ := fun f g x => g (f x)
  |}.

(* 例 *)
Check Hom : Set -> Set -> Set.
Check comp (mult 2) (mult 3) : Hom nat nat.
Check (plus 2) \; (mult 3) : nat ~> nat.
Check (plus 2) \; (mult 3) : nat ~{SETS}~> nat.
Check (mult 3) \o (plus 2) : nat ~> nat.
Check (mult 3) \o (plus 2) : nat ~{SETS}~> nat.
Compute ((mult 3) \o (plus 2)) 1.           (* 3 * (2 + 1) *)


(* 関手 *)
Require Import Coq.Logic.FunctionalExtensionality.

Generalizable Variables Obja Homa Objb Homb.

Class Functor `(Ca : @Category Obja Homa) `(Cb : @Category Objb Homb) : Type :=
  {
    a : Obja;
    b : Objb;
    fobj : Obja -> Objb;
    fmor : Homa a a -> Homb b b;
    fmor_comp : forall (m n : a ~{Ca}~> a), fmor m \; fmor n = fmor (m \; n)
  }.
    
Definition Fobj (a : unit) : Set := nat.
Check Fobj tt : Set.
Compute Fobj tt.                            (* nat *)

Definition Fmor (n : tt ~{SPLUS}~> tt) : nat ~{SETS}~> nat := fun x => n + x.
Check (Fmor 1) \; (Fmor 2) : nat ~{SETS}~> nat.
Compute (Fmor 1) \; (Fmor 2).               (* fun x => x + 3 *)

Program Instance F : Functor SPLUS SETS :=
  {|
    a := tt;
    b := nat;
    fobj := Fobj;
    fmor := Fmor
  |}.
Obligation 1.
Proof.
  unfold Fmor.
  simpl.
  Check @functional_extensionality_dep.
  Check functional_extensionality_dep
        (fun x : nat => n + (m + x)) (fun x : nat => m + n + x).
  eapply functional_extensionality_dep.
  intro x.
  now rewrite plus_assoc.
Qed.

(*
Goal forall (m n : tt ~{SPLUS}~> tt), Fmor m \; Fmor n = Fmor (m \; n).
Proof.
  intros m n.
  unfold Fmor.
  simpl.
  Check @functional_extensionality_dep.
  Check functional_extensionality_dep
        (fun x : nat => n + (m + x)) (fun x : nat => m + n + x).
  eapply functional_extensionality_dep.
  intro x.
  now rewrite plus_assoc.
Qed.
*)
  
(* この方向の関手は、一般的には定義できない。 *)
Definition G (f : nat ~{SETS}~> nat) : tt ~{SPLUS}~> tt := f 0.
Check (G (plus 1)) \; (G (plus 2)) : tt ~{SPLUS}~> tt.
Compute (G (plus 1)) \; (G (plus 2)).       (* 3 *)

Goal forall (f g : nat ~{SETS}~> nat), G f \; G g = G (f \; g).
Proof.
  intros f g.
  unfold G.
  simpl.
Admitted.

(* ************* *)
(* 半順序集合の圏 *)
(* ************* *)
Definition Hom21 (m n : nat) : Set := m <= n.
Definition id21 (n : nat) : Hom21 n n.
Proof.
  unfold Hom21. easy.                        (* omega でなく *)
Defined.
Definition comp21 {m n p} H1 H2 := le_trans m n p H1 H2.

Program Instance P_LE : @Category nat Hom21 :=
  {|
    id := id21;
    comp nat  _ _ := comp21
  |}.
Obligation 1.
Proof.
  unfold Hom21 in *.
  apply proof_irrelevance.
Qed.
Obligation 2.
Proof.
  unfold Hom21 in *.
  apply proof_irrelevance.
Qed.
Obligation 3.
Proof.
  unfold Hom21 in *.
  apply proof_irrelevance.
Qed.


Definition Hom22 (m n : nat) : Set := n <= m.
Definition id22 (n : nat) : Hom22 n n.
Proof.
  unfold Hom22. easy.                        (* omega でなく *)
Defined.
Definition comp22 {m n p} H1 H2 := le_trans p n m H2 H1.

Program Instance P_GE : @Category nat Hom22 :=
  {|
    id := id22;
    comp nat  _ _ := comp22
  |}.
Obligation 1.
Proof.
  unfold Hom22 in *.
  apply proof_irrelevance.
Qed.
Obligation 2.
Proof.
  unfold Hom22 in *.
  apply proof_irrelevance.
Qed.
Obligation 3.
Proof.
  unfold Hom22 in *.
  apply proof_irrelevance.
Qed.


(* 例 *)
Definition le34 : 3 ~{P_LE}~> 4. Proof. unfold Hom, Hom21. omega. Defined.
Definition le45 : 4 ~{P_LE}~> 5. Proof. unfold Hom, Hom21. omega. Defined.
Check le34 \; le45 : 3 ~> 5.
Check le34 \; le45 : 3 ~{P_LE}~> 5.

Definition ge43 : 4 ~{P_GE}~> 3. Proof. unfold Hom, Hom22. omega. Defined.
Definition ge54 : 5 ~{P_GE}~> 4. Proof. unfold Hom, Hom22. omega. Defined.
Check ge54 \; ge43 : 5 ~> 3.
Check ge54 \; ge43 : 5 ~{P_GE}~> 3.

(* 関手もどき。compの引数が逆転するので、関手の規則を満たしていない。 *)
Definition F2 {m n : nat} (f : m ~{P_LE}~> n) : n ~{P_GE}~> m.
Proof.
  unfold Hom, Hom21, Hom22 in *.
  easy.
Defined.
Check F2 le34 : 4 ~{P_GE}~> 3.
Goal forall (m n p : nat) (f : m ~{P_LE}~> n) (g : n ~{P_LE}~> p),
    F2 g \; F2 f = F2 (f \; g).
Proof.
  intros.
  unfold Hom, Hom21, Hom22 in *.
  apply proof_irrelevance.
Qed.

Definition G2 {m n : nat} (f : m ~{P_GE}~> n) : n ~{P_LE}~> m.
Proof.
  unfold Hom, Hom21, Hom22 in *.
  easy.
Defined.
Goal forall (m n p : nat) (f : m ~{P_GE}~> n) (g : n ~{P_GE}~> p),
    G2 g \; G2 f = G2 (f \; g).
Proof.
  intros.
  unfold Hom, Hom21, Hom22 in *.
  apply proof_irrelevance.
Qed.


(* *********** *)
(* しりとりの圏 *)
(* *********** *)
Inductive Hira : Set := こ | ぶ | た | ぬ | き | つ | ね.
Inductive Hom3 : Hira -> Hira -> Set :=
  | single : forall A, Hom3 A A
  | cons : forall {A' B : Hira} (A : Hira) (tl : Hom3 A' B), Hom3 A B.

Definition comp3 {A B C : Hira} (f : Hom3 A B) (g : Hom3 B C) : Hom3 A C.
Proof.
  intros.
  induction f.
  + easy.
  + Check (cons A (IHf g)).
    apply (cons A (IHf g)).
Defined.

Program Instance SIRI : @Category Hira Hom3 :=
  {|
    id := single;
    comp _ _ _ := comp3
  |}.
Obligation 2.
  intros.
  induction f.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHf.
    reflexivity.
Qed.
Obligation 3.
Proof.
  induction f.
  + easy.
  + simpl.
    now rewrite IHf.
Qed.

(* 例 *)
Definition こぶた := cons こ (cons ぶ (single た)) : Hom こ た.
Definition たぬき := cons た (cons ぬ (single き)) : Hom た き.
Check comp こぶた たぬき : Hom こ き.
Compute comp こぶた たぬき.        (* こ ぶ た ぬ き : Home こ き *)
Check こぶた \; たぬき  : こ ~> き.
Check こぶた \; たぬき : こ ~{SIRI}~> き.

(* END *)
