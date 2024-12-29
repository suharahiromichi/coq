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
    rewrite /injective => x1 x2.
    have H x y : x = y -> x - 3 = y - 3 by move=> ->.
    move/H.
    rewrite -2![_ + 3 - 3]addrA.
    have -> x : x - x = 0 by apply/eqP; rewrite subr_eq0.
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

(**
## Musketeer type 三銃士型
 *)
  Inductive Musketeer :=
  | athos
  | porthos
  | aramis.

  Definition f (x : Musketeer) : Musketeer :=
    match x with
    | athos => aramis
    | porthos => aramis
    | aramis => athos
    end.

  Goal ~ injective f.
  Proof.
    rewrite /injective.
    move/(_ athos porthos)/(_ erefl).
    Check (aramis = aramis -> athos = porthos) -> False.
    (* -> の右が /(_ erefl) で消える。 *)
    done.
  Qed.
  
  Goal ~ surjective f.
  Proof.
    rewrite /surjective.
    move/(_ porthos) => [].
    by case.                     (* x を三つの要素で場合分けする。  *)
    (* どれも = porthos にならない。 *)
  Qed.

  Definition g (x : Musketeer) : Musketeer :=
    match x with
    | athos => porthos
    | porthos => aramis
    | aramis => athos
    end.

  Goal injective g.
  Proof.
    by case; case.
  Qed.

  Goal surjective g.
  Proof.
    case.
    - exists aramis => //=.
    - exists athos => //=.
    - exists porthos => //=.
  Qed.
  
(**
## ``x |-> x^3`` は単射である。
*)
  (* 公理 *)
  (* Mathcomp では、integral domain でないと成り立たないか。 *)
  Axiom ax : forall (a b : R), (a * b == 0) = (a == 0) || (b == 0).
  
  (* 便利な補題 *)
  Lemma ltF (x : R) : (x < x) = false.
  Proof.
    apply/negP.
    move/lt_eqF.
    rewrite eq_refl.
    done.
  Qed.
  
  Lemma lt0_le0 (x : R) : 0 < x -> 0 <= x.
  Proof.
    rewrite lt0r //=.
    case/andP.
    done.
  Qed.
  
  (* の結論だけ対偶を取る。 *) (* notu *)
  Check @paddr_eq0 R : forall x y : R, 0 <= x -> 0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
  Lemma paddr_eq0' (x y : R) : 0 <= x -> 0 <= y -> (x + y != 0) = (x != 0) || (y != 0).
  Proof.
    move=> Hx0 Hy0.
    by rewrite paddr_eq0 //= negb_and.
  Qed.
  
  Check @addr_ge0 R : forall (x y : R), 0 <= x -> 0 <= y -> 0 <= x + y.
  Lemma addr_gt0_ge0 (x y : R) : 0 < x -> 0 <= y -> 0 < x + y.
  Proof.
    move=> H0ltx H0ley.
    rewrite lt0r.
    apply/andP.
    split.
    
    Check x + y != 0.
    - suff -> : 0 < x -> x + y != 0 => //=.
      rewrite lt0r.
      case/andP => Hxn0 H0le0.
      rewrite paddr_eq0 //= negb_and.
      by apply/orP/or_introl.      
      
    Check 0 <= x + y.
    - move/lt0_le0 in H0ltx.
      by apply: addr_ge0.
  Qed.
  
  (* 計算 *)
  Lemma calc1 (x1 x2 : R) : (x1 - x2) * (x1 ^+ 2 + x1 * x2 + x2 ^+ 2) = x1 ^+ 3 - x2 ^+ 3.
  Proof.
    ring.
  Qed.
  
  Lemma calc2 (x1 x2 : R) : 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = x1 ^+ 2 + ((x1 + x2) ^+ 2 + x2 ^+ 2).
  Proof.
    ring.
  Qed.
  
  Lemma calc3 (x1 x2 : R) : x1 <> 0 -> 0 < x1 ^+ 2 + ((x1 + x2) ^+ 2 + x2 ^+ 2).
  Proof.
    move=> H.
    apply: addr_gt0_ge0; [| apply: addr_ge0].
    - rewrite exprn_even_gt0 //=.
      by apply/eqP.
    - exact: sqr_ge0.
    - exact: sqr_ge0.
  Qed.

  Goal injective (fun (x : R) => x ^+ 3).
  Proof.
    move=> x1 x2 H.

    (* 前提を因数分解する。 *)
    have : (x1 - x2) * (x1 ^+ 2 + x1 * x2 + x2 ^+ 2) = 0 by rewrite calc1 H; ring.
    move/eqP.
    rewrite ax.
    case/orP => /eqP.

    Check x1 - x2 = 0.
    - by move/subr0_eq.

    Check x1 ^+ 2 + x1 * x2 + x2 ^+ 2 = 0.
    - case Hx1 : (x1 == 0); move/eqP in Hx1.

      Check Hx1 : x1 = 0.                   (* の場合 *)
      + rewrite Hx1 expr0n /= add0r mul0r add0r.
        move/eqP.
        by rewrite expf_eq0 => /andP [] _ /eqP.
        
      Check Hx1 : x1 <> 0.                  (* の場合 *)
      + move=> H'.
        Check H' : x1 ^+ 2 + x1 * x2 + x2 ^+ 2 = 0.
        (* これに対して、以下を証明して、前提矛盾を導く。 *)
        suff : x1 ^ 2 + x1 * x2 + x2 ^ 2 > 0 by rewrite H' ltF.
        by rewrite -(pmulr_rgt0 (x:=2)) //= calc2 calc3.
  Qed.

(**
## Exercise
*)
  Goal injective (fun (x : rat) => x - 12).
  Proof.
    move=> x1 x2.
    have H (x y : rat) : x = y -> x + 12 = y + 12 by move=> ->.
    move/H.
    rewrite -2!addrA.
    have -> : -12 + 12 = 0 :> rat by done.
    by rewrite 2!addr0.
  Qed.
  
  Goal ~ injective (fun (x : R) => (3 : R)).
  Proof.
    Check 3 = 3 -> 0 = 3 -> False.
    have H : 3 = 3 :> R by ring.
    move/(_ 0 3 H)/eqP.
    have -> : (0 == 3 :> R) = false by apply: lt_eqF.
    done.
  Qed.

  Lemma addIf : forall (R : idomainType) (a : R), injective (+%R^~ a).
  Proof.
    move=> R' a x1 x2.
    have H x y : x = y -> x - a = y - a by move=> ->.
    move/H.
    rewrite -2!addrA.
    have -> : a - a = 0 by ring.
    by rewrite 2!addr0.
  Qed.
  
  (* see. ssralg.v *)
  Lemma mulfI : forall (R : idomainType) (a : R), a != 0 -> injective (fun x => a * x).
  Proof.
    move=> R0 x nz_x x1 x2.
    apply: contra_eq => neq_yz.
    rewrite -subr_eq0.
    rewrite -mulrBr.
    Check x * (x1 - x2) != 0.
    rewrite mulf_neq0 //=.
    rewrite subr_eq0.
    done.
  Qed.
  
  Goal injective (fun (x : int) => 3 * x - 1).
  Proof.
    move=> x1 x2.
    lia.

    Restart.
    have H3n0 : 3 != 0 :> int by lia.
    move=> x1 x2 H.
    apply/(mulfI H3n0)/addIf/H.
    Restart.
    
    move=> x1 x2 H.
    Check @mulfI int 3 _ x1 x2 : 3 * x1 = 3 * x2 -> x1 = x2.
    Check @addIf int (-1) (3 * x1) (3 * x2) : 3 * x1 - 1 = 3 * x2 - 1 -> 3 * x1 = 3 * x2.
    apply: (@mulfI int 3 _ x1 x2) => //=.
    apply: (@addIf int (-1) (3 * x1) (3 * x2)).
    done.
  Qed.
  
End Functions.

(* END *)
