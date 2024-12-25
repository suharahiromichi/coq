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
Import Order.Theory.

Open Scope ring_scope.

Import intZmod.                             (* addz など *)
Import intRing.                             (* mulz など *)

Section Sample.

  Variable R : realDomainType.
  Variable x y z : R.
  
  Check lerN10 R : -1 <= 0.
  Check @gtrN R x : 0 < x -> - x < x.
  Check lerN2 x y : (- x <= - y) = (y <= x).
  Check ltrN2 x y : (- x < - y) = (y < x).
  Check lerNr x y : (x <= - y) = (y <= - x).
  Check @real_neqr_lt R x y.

End Sample.


Section Functions.

  Variable R : realDomainType.
  
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
    - by apply/orP/or_introl/gtrN.
    - rewrite realE.
      by apply/orP/or_intror/lerN10.
    - done.
  Qed.
  
  Goal ~ injective  (fun x : R => x^+2).
  Proof.
    rewrite /injective.
    have H : (- 1) ^+ 2 = 1 ^+ 2 :> R by ring.
    move/(_ (- 1) 1 H).
    by move/neq1N1.
  Qed.
  
  Definition surjective (rT aT : Type) (f : aT -> rT) := forall y, exists x, f x = y.
  
  Goal surjective (fun (a : rat) => 3 * a + 2).
  Proof.
    rewrite /surjective => y.
    exists ((y - 2) / 3).
    have -> (a : rat) : 3 * (a / 3) = a
      by rewrite mulrA [3 * a]mulrC -mulrA divff; first rewrite mulr1.
    ring.
  Qed.
  
  Lemma ne_of_gt (a b : R) : b < a -> a != b.
  Proof.
    move=> H.
    rewrite real_neqr_lt //=.
    by apply/orP/or_intror.
  Qed.

  Goal ~ surjective  (fun x : R => x^+2).
  Proof.
    rewrite /surjective.
    move/(_ (- 1)).
    case=> x.
    apply/eqP/ne_of_gt.
    Check sqr_ge0 x : 0  <= x ^+ 2.
    Check ltrN10 R : -1 < 0.
    apply: lt_le_trans.
    - exact (ltrN10 R).
    - exact (sqr_ge0 x).
  Qed.
  
End Functions.

(* END *)
