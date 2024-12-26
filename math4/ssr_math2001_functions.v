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

Section Sample.

  Variable R : realDomainType.
  Variable x y z : R.
  
  (* order *)
  Check @lt_eqF : forall (disp : unit) (T : porderType disp) (x y : T), (x < y)%O -> (x == y) = false.
  Check @gt_eqF : forall (disp : unit) (T : porderType disp) (x y : T), (y < x)%O -> (x == y) = false.

  (* ssrnum *)
  Check lerN10 R : -1 <= 0.
  Check @gtrN R x : 0 < x -> - x < x.
  Check lerN2 x y : (- x <= - y) = (y <= x).
  Check ltrN2 x y : (- x < - y) = (y < x).
  Check lerNr x y : (x <= - y) = (y <= - x).
  
  Check @real_ltNge R : {in Num.real &, forall x y : R, (x < y) = ~~ (y <= x)}.
  Check @real_leNgt R : {in Num.real &, forall x y : R, (x <= y) = ~~ (y < x)}.
  Check @real_neqr_lt R : {in Num.real &, forall x y : R, (x != y) = (x < y) || (y < x)}.
  
(**
使用例：
*)
  Lemma ne_of_gt (a b : R) : b < a -> a != b.
  Proof.
    move=> H.
    rewrite real_neqr_lt //=.
    by apply/orP/or_intror.
    Undo 2.
    apply/negbT.
    by rewrite gt_eqF.
  Qed.

End Sample.


Section Functions.

  Variable R : realDomainType.
  
(**
## 単射
*)
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
    Search ((- _) = _).
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
  
(**
## 全射
*)
  Definition surjective (rT aT : Type) (f : aT -> rT) := forall y, exists x, f x = y.
  
  Goal surjective (fun (a : rat) => 3 * a + 2).
  Proof.
    rewrite /surjective => y.
    exists ((y - 2) / 3).
    have -> (a : rat) : 3 * (a / 3) = a
      by rewrite mulrA [3 * a]mulrC -mulrA divff; first rewrite mulr1.
    ring.
  Qed.
  
  Goal ~ surjective  (fun x : R => x^+2).
  Proof.
    rewrite /surjective.
    move/(_ (- 1)).
    case=> x.
    apply/eqP/negbT.
    rewrite gt_eqF //=.
    Check sqr_ge0 x : 0  <= x ^+ 2.
    Check ltrN10 R : -1 < 0.
    apply: lt_le_trans.
    - exact (ltrN10 R).
    - exact (sqr_ge0 x).
  Qed.
  
End Functions.

(* END *)
