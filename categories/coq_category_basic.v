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
Definition comp0 (m n : Hom0 tt tt) := m + n.  
Check comp0 1 2 : Hom0 tt tt.
Compute comp0 1 2.                          (* 3 *)

(* 恒等射 identity *)
Definition id0 : Hom0 tt tt := 0.

(* 単位元律 unit law 01 *)
Theorem unit0_l : forall (n : nat), comp0 id0 n = n.
Proof.
  intros.
  reflexivity.
Qed.

(* 単位元律 unit law 02 *)
Theorem unit0_r : forall (n : nat), comp0 n id0 = n.
Proof.
  intros.
  unfold id0, comp0.
  Search _ (_ + 0 = _).
  apply Nat.add_0_r.
Qed.

(* 結合律 associative low *)
Theorem assoc1 : forall m n p,
    comp0 m (comp0 n p) = comp0 (comp0 m n) p.
Proof.
 intros.
 unfold id0, comp0.
 Search _ (_ + _ + _ = _).
 apply plus_assoc.
Qed.


(* Cat1 集合の圏 *)
Definition Hom1 (A B : Set) : Set := A -> B.
Check Hom1 : Set -> Set -> Set.
Check plus 1 : Hom1 nat nat.
Check plus 2 : Hom1 nat nat.
Definition comp1 {A B C : Set} (f : Hom1 B C) (g : Hom1 A B) := fun x => f (g x).
Check comp1 (plus 1) (plus 2) : Hom1 nat nat.
Compute comp1 (plus 1) (plus 2).            (* fun x : x + 3 *)


(* 恒等射 identity *)
Definition id1 : Hom1 nat nat := plus 0.

(* 単位元律 unit law 01 *)
Theorem unit1_l : forall (n : nat), comp1 id1 (plus n) = plus n.
Proof.
  intros.
  reflexivity.
Qed.

(* 単位元律 unit law 02 *)
Theorem unit1_r : forall (n : nat), comp1 (plus n) id1 = plus n.
Proof.
  intros.
  reflexivity.
Qed.

(* 結合律 associative low *)
Theorem assoc1 : forall m n p,
    comp1 (plus m) (comp1 (plus n) (plus p)) =
    comp1 (comp1 (plus m) (plus n)) (plus p).
Proof.
 intros.
 reflexivity.
Qed.


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

(* 恒等射 identity *)
Definition id2 (n : nat) : Hom2 n n. Proof. unfold Hom2. easy. Defined.

(* 単位元律 unit law 01 *)
Theorem unit2_l : forall (m n : nat) (f : Hom2 m n),
    comp2 (id2 m) f = f.                    (* irrelevance が必要 *)
Proof.
  unfold Hom2.
  intros.
  unfold id2, comp2.
  Check Nat.le_trans.
  Admitted.

(* 単位元律 unit law 02 *)
(* TODO *)

(* 結合律 associative low *)
(* TODO *)


(* Cat3 しりとりの圏 *)
Inductive Hira : Set := こ | ぶ | た | ぬ | き | つ | ね.
Inductive Hom3 : Hira -> Hira -> Set := siri : forall (a b : Hira), Hom3 a b.
Check Hom3 : Hira -> Hira -> Set.
Definition こた := siri こ た : Hom3 こ た.
Definition たき := siri た き : Hom3 た き.
Definition comp3 {A B C : Hira} (f : Hom3 A B) (g : Hom3 B C) : Hom3 A C.
Proof. easy. Defined.
Check comp3 こた たき : Hom3 こ き.
Compute comp3 こた たき.                  (* siri こ き : Home3 こ き *)

(* 恒等射 identity *)
Definition id3 A : Hom3 A A := siri A A.

(* 単位元律 unit law 01 *)
Theorem unit3_l : forall (A B : Hira), comp3 (id3 A) (siri A B) = siri A B.
Proof.
  intros.
  reflexivity.
Qed.

(* 単位元律 unit law 02 *)
Theorem unit3_r : forall (A B : Hira), comp3 (siri A B) (id3 B) = siri A B.
Proof.
 intros.
 reflexivity.
Qed.

(* 結合律 associative low *)
Theorem assoc3 : forall A B C D,
    comp3 (siri A B) (comp3 (siri B C) (siri C D)) =
    comp3 (comp3 (siri A B) (siri B C)) (siri C D).
Proof.
 intros.
 reflexivity.
Qed.

(* END *)
