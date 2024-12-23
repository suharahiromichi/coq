(**
The Mechanics of Proof

https://hrmacbeth.github.io/math2001/08_Functions.html
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Print set_surj.                             (* 全射 *)
Print set_inj.                              (* 単射 *)
Print set_bij.                              (* 全単射 *)

Section Functions.

  Variable Rt : ringType.
  Variable R : (set Rt).
  
  Definition q (x : Rt) := x + 3.

  Goal set_inj R q.
  Proof.
    rewrite /set_inj => x y Hx Hy.
    rewrite /q.
    have H : {homo (fun (x : Rt) => x - 3) : a b / a = b} by move=> a b ->.
    move/H.
    rewrite -2!GRing.addrA.
    have -> a : a - a = 0 by apply/eqP; rewrite GRing.subr_eq0.
    rewrite 2!GRing.addr0.
    by move ->.
  Qed.
  
  
End Functions.

(* END *)
