(**
The Mechanics of Proof

https://hrmacbeth.github.io/math2001/08_Functions.html
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_classical.
From mathcomp Require Import zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

Open Scope ring_scope.

Import intZmod.                             (* addz など *)
Import intRing.                             (* mulz など *)

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
    rewrite -2!addrA.
    have -> a : a - a = 0 by apply/eqP; rewrite subr_eq0.
    rewrite 2!addr0.
    by move ->.
  Qed.

End Functions.

Section f.
  Variable R : numDomainType.
  
  Goal injective (fun x : R => x + 3).
  Proof.
    rewrite /injective => x y.
    have H a b : a = b -> a - 3 = b - 3 by move=> ->.
    move/H.
    rewrite -2![_ + 3 - 3]addrA.
    have -> a : a - a = 0 by apply/eqP; rewrite subr_eq0.
    rewrite 2!addr0.
    by move ->.
  Qed.

  Lemma neq1N1 : (- 1) <> 1 :> R.
  Proof.
    apply/eqP.
    rewrite real_neqr_lt.
    - apply/orP/or_introl.
      by apply gtrN.   
    - Check (-1 \is Num.real).
      Search (_ \is Num.real).
      rewrite realE.
      apply/orP.
      right.
      by apply: lerN10.
    - done.
  Qed.
  
  Goal ~injective  (fun x : R => x^+2).
  Proof.
    rewrite /injective.
    have H : (- 1) ^+ 2 = 1 ^+ 2 :> R by ring.
    move/(_ (- 1) 1 H).
    by move/neq1N1.
  Qed.
  
End f.

(* END *)
