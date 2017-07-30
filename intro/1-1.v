(* Suhara for PF *)
(* About integer powers (monomorphic version) *)

Set Implicit Arguments.

Require Import ZArith.

Require Import Div2.

Require Import Program.

Open Scope Z_scope.

Fixpoint power (a:Z)(n:nat) :=
  match n with
  | 0%nat => 1
  | S p =>  a * power a p
  end.

Eval vm_compute in power 2 40.              (* = 1099511627776 : Z *)

Require Import Recdef.
Function binary_power_mult' (acc x:Z) (n:nat) {measure (fun i => i) n} : Z :=
  match n with 
    | 0%nat => acc
    | _ => if Even.even_odd_dec n
           then binary_power_mult' acc (x * x) (div2 n)
           else binary_power_mult' (acc * x) (x * x) (div2 n)
  end.
Proof.
  intros.
  Check lt_div2 : forall n : nat, (0 < n)%nat -> (Nat.div2 n < n)%nat.
  apply lt_div2.
  debug auto with arith.
  Undo 1.
  now apply Nat.lt_0_succ.
  
  (* おなじ *)
  intros.
  apply lt_div2.
  (* 0 < S n0 *)
  omega.
Qed.

Program
Fixpoint binary_power_mult (acc x:Z) (n:nat) {measure n} : Z
  (* acc * (power x n) *) :=
  match n with 
    | 0%nat => acc
    | _ => if Even.even_odd_dec n
           then binary_power_mult acc (x * x) (div2 n)
           else binary_power_mult (acc * x) (x * x) (div2 n)
  end.
Solve Obligations with program_simpl; intros; apply lt_div2; omega. (* auto with arith. *)


Definition binary_power (x:Z)(n:nat) := binary_power_mult 1 x n.

Eval vm_compute in binary_power 2 40.       (* = 1099511627776 : Z *)

Goal binary_power 2 234 = power 2 234.
  reflexivity.
Qed.
(* binary_powe function and the naive power function are pointwise equivalent. *)

(* END *)
