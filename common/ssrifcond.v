From mathcomp Require Import all_ssreflect.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ゴールと前提にある if式の条件で場合分けする。 *)
Ltac if_condition' :=
  intros;
  repeat match goal with
         | [ |- context[if ?b then _ else _] ] =>
           let H' := fresh in destruct b eqn: H'
         | [ H : context[if ?b then _ else _] |- _ ] =>
           let H' := fresh in destruct b eqn: H'
         | _ => idtac
         end.

Ltac if_condition :=
  if_condition'; try done; ssromega.

(* Sample *)
Goal forall m n, (if m < n then m else n) = (if n <= m then n else m).
Proof.
  if_condition.
Qed.

(* END *)
