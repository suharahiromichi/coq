From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
sigma type は、証人と証拠の組のことだが、証拠がboolの式であるとき、 
boolean sigma type (sigma type with boolean specifiations) という。
 *)

Check odd : pred nat.

Definition odds := {x : nat | odd x}.       (* booelan sigma type *)

(**
証人(witness) が同じでも、証拠の異なるふたつの数、one_odd1とone_odd2 がある。
  *)
Definition one_odd1 : odds.
Proof.
    by exists 1.
Defined.
Print one_odd1.    (* = exist (fun x : nat => odd x) 1 is_true_true *)
Print is_true_true.
Print erefl.
Print Logic.eq_refl.                        (* ∀x. x = x *)

Definition one_odd2 : odds.
Proof.
    by exists 1; rewrite -(addn0 1) addn0.  (* 1+0-0 *)
Defined.
Print one_odd2.    (* = exist (fun x : nat => odd x) 1 ...略... *)

(**
one_odd1 の証拠は is_true_true すなわち true = true 。
one_odd2 の証拠も同様に boolの等式の形である。
（同じ型の）等式どうしは等しいという定理 irrelevance を使って証明できる。

的外れ、見当違いの意味。
 *)

Goal one_odd1 = one_odd2.
  try reflexivity.                       (* still not convertible *)
  congr exist.                           (* (true = true) = 略 *)
  by apply: bool_irrelevance.
Qed.

(**
Mathcomp では、次の irrelevance が使える。
より一般的な eqType について証明されていて、natとboolはそれを使って証明している。
*)
Check eq_irrelevance   : forall (T : eqType) (x y : T)    (e1 e2 : x = y), e1 = e2.
Check bool_irrelevance : forall              (x y : bool) (E  E' : x = y), E = E'.
Check nat_irrelevance  : forall              (x y : nat)  (E  E' : x = y), E = E'.

(**
不等式についても成り立つ。
 *)
Check le_irrelevance :
  forall (m n : nat) (le_mn1 le_mn2 : (m <= n)%coq_nat), le_mn1 = le_mn2.
Check lt_irrelevance :
  forall (m n : nat) (lt_mn1 lt_mn2 : (m < n)%coq_nat),  lt_mn1 = lt_mn2.

(* END *)
