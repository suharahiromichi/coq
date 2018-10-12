(**
シングルトン
対象の型  unit
対象      tt（のみ）
射の型    Hom := ∀a b : unit, nat
射の型    Hom tt tt  (= nat)
射の例    1, 2

集合の圏
対象の型  Set
対象      nat（のみ）
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
*)

Require Import Omega.

(* Cat0 シングルトン *)
Definition Hom0 (A B : unit) : Set := nat.
Check Hom0 : unit -> unit -> Set.
Check 1 : Hom0 tt tt.
Check 2 : Hom0 tt tt.
Definition comp0 (m n : Hom0 tt tt) := m + n.  
Check comp0 1 2 : Hom0 tt tt.
Compute comp0 1 2.                          (* 3 *)

(* Cat1 集合の圏 *)
Definition Hom1 (A B : Set) : Set := A -> B.
Check Hom1 : Set -> Set -> Set.
Check plus 1 : Hom1 nat nat.
Check plus 2 : Hom1 nat nat.
Definition comp1 {A B C : Set} (f : Hom1 B C) (g : Hom1 A B) := fun x => f (g x).
Check comp1 (plus 1) (plus 2) : Hom1 nat nat.
Compute comp1 (plus 1) (plus 2).            (* fun x : x + 3 *)

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

(* END *)
