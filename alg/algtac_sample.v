From Coq Require Import ZifyClasses ZArith_base.
From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint rat intdiv.
From mathcomp Require Import ssrZ zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

Open Scope ring_scope.

(**
# [lia]: 線形整数算術（プレスバーガー算術）のソルバ
*)
Goal forall m n : nat, (n <= m -> n.*2 <= m + n)%N.
Proof. lia. Qed.

Goal forall m n : int, n <= m -> n * 2 <= m + n.
Proof. lia. Qed.

Goal forall m n : int,
    27 <= 11 * m + 13 * n <= 45 -> -10 <= 7 * m - 9 * n <= 4 -> False.
Proof. lia. Qed.

Goal forall m n : nat, (n <= m)%N = ~~ (m.*2 < n.*2)%N.
Proof. lia. Qed.

Goal forall m n : int, n <= m = ~~ (m * 2 < n * 2).
Proof. lia. Qed.

Goal forall m n : nat, m * n = n * m.
Proof. lia. Qed.

Goal forall m n : nat, ((m + n) ^ 2 = m ^ 2 + n ^ 2 + 2 * m * n)%N.
Proof. lia. Qed.

(* 自然数の割り算 *)
Goal forall m : nat, (m %/ 2 <= m)%N.
Proof. lia. Qed.

Goal forall m : nat, 6 %| m -> 4 %| m -> 12 %| m.
Proof. lia. Qed.

Goal forall m : nat, (6 %| m) && (4 %| m) = (12 %| m).
Proof. lia. Qed.

(**
# [nia]: 非線形整数算術のソルバ
*)
Goal forall m n : int, 0 <= m -> 0 <= n -> 0 <= m * n.
Proof. nia. Qed.

Goal forall (m : int) (n : nat), 0 <= (m ^+ 2) ^+ n.
Proof. nia. Qed.

Goal forall m n : nat, (n <= m -> n ^ 2 <= m * n)%N.
Proof. nia. Qed.

Goal forall m n p : int,
    0 <= n -> (m %/ (n * p))%Z = ((m %/ n) %/ p)%Z.
Proof. nia. Qed.

Definition triple (n : nat) : nat := n * 3.

Fact Op_triple_subproof (n : nat) : (Z.of_nat (triple n) = 3 * Z.of_nat n)%Z.
Proof. rewrite /triple; lia. Qed.

#[global]
  Instance Op_triple : UnOp triple := {
    TUOp := Z.mul 3;
    TUOpInj := Op_triple_subproof
    }.
  
  Add Zify UnOp Op_triple.

Goal forall (n : nat), triple (triple n) = n * 9.
Proof. lia. Qed.

(**
# [ring]: 多項式の等式のソルバ
*)
Goal forall a b : int, (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2 * a * b :> int.
Proof. move=> a b; ring. Qed.

Goal forall a b : rat, (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2 * a * b :> rat.
Proof. move=> a b; ring. Qed.

Goal forall (R : comRingType) (a b : R),
    (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2 * a * b :> R.
Proof. move=> R a b; ring. Qed.

Goal forall (R : comRingType) (a : R) (b : R * int),
    ((a, 1) + b) ^+ 2 = (a, 1) ^+ 2 + b ^+ 2 + 2 * (a, 1) * b :> R * int.
Proof. move=> R a b; ring. Qed.

Goal forall a b : int, a * b = 15 -> (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 30.
Proof. lia. Qed.

Goal forall (R : ringType) (S : comRingType) (f : {rmorphism R -> S}) (a b : R),
    f ((a + b) ^+ 2) = f a ^+ 2 + f b ^+ 2 + 2 * f a * f b.
Proof.
  move=> R S f a b.
  (* rewrite rmorphX rmorphD. *)
  ring.
Qed.

(**
# [field]: 有理等式のソルバ
*)
Goal forall (F : fieldType) (x : F),
    x != 0 -> (1 - 1 / x) * x - x + 1 = 0.
Proof.
  move=> F x x_neq0.
  field.
  exact: x_neq0.
Qed.

Goal forall (F : fieldType) (n : nat),
    n%:R != 0 :> F -> (2 * n)%:R / n%:R = 2 :> F.
Proof.
  move=> F n n_neq0.
  field.
  exact: n_neq0.
Qed.

Goal forall (F : numFieldType) (x : F), (x / 2) * 2 = x.
Proof.
  move=> F x.
  field.
  by [].
Qed.

Goal forall (x y : int), y <= x -> 0 <= x -> y <= x * 2.
Proof. move=> R x y; lra. Qed.

Goal forall (x y : rat), y <= x -> 0 <= x -> y / 2 <= x.
Proof. move=> R x y; lra. Qed.

Goal forall (R : realDomainType) (x y : R),
    x + 2 * y <= 3 -> 2 * x + y <= 3 -> x + y <= 2.
Proof. move=> R x y; lra. Qed.

(* END *)
