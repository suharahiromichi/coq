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
    have : (x1 - x2) * (x1 ^+ 2 + x1 * x2 + x2 ^+ 2) = 0 by rewrite calc1 H; ring.
    move/eqP.
    rewrite ax.
    case/orP => /eqP.
    - by move/subr0_eq.
    - case Ha1 : (x1 == 0); move/eqP in Ha1.
      + rewrite Ha1 expr0n /= add0r mul0r add0r.
        move/eqP.
        by rewrite expf_eq0 => /andP [] _ /eqP.
        
      + have H3 : x1 ^+ 2 + ((x1 + x2) ^+ 2 + x2 ^+ 2) > 0 by apply: calc3.
        have H4 : 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) > 0 by rewrite calc2 H3.
        have H5 : x1 ^ 2 + x1 * x2 + x2 ^ 2 > 0 by rewrite -(pmulr_rgt0 (x:=2)).
        move=> H6.
        move: H5.
        rewrite H6.
        by rewrite ltF.
  Qed.

  (* ********************************* *)
  
(*
  Lemma test (x : R) : ~~ (x < x).
  Proof.
    apply/negP.
    move/lt_eqF.
    rewrite eq_refl.
    done.
  Qed.

  Lemma test2 (x : R) : (x < x) = false.
  Proof.
    apply/negP.
    move/lt_eqF.
    rewrite eq_refl.
    done.
  Qed.
  
  Lemma test3 (x1 x2 : R) : (x1 - x2) * (x1 ^+ 2 + x1 * x2 + x2 ^+ 2) = x1 ^+ 3 - x2 ^+ 3.
  Proof.
    ring.
  Qed.
  
  Lemma test4 (x1 x2 : R) : 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = x1 ^+ 2 + ((x1 + x2) ^+ 2 + x2 ^+ 2).
  Proof.
    ring.
  Qed.
  
  Search (0 < _ + _).
  Search "addr".

  Lemma addr_ge0 (x y : R) : 0 <= x -> 0 <= y -> 0 <= x + y.
  Proof.
    rewrite le0r.
    Check (x == 0) || (0 < x) -> 0 <= y -> 0 <= x + y.
    Check @predU1P : forall (T : eqType) (x y : T) (b : bool), reflect (x = y \/ b) ((x == y) || b).

    case/predU1P=> [-> | x_pos]; rewrite ?add0r // le0r.
    by case/predU1P=> [-> | y_pos]; rewrite ltW ?addr0 ?addr_gt0.
  Qed.

  Check paddr_eq0. (* の結論だけ対偶を取る。 *)
  Lemma paddr_eq0' (x y : R) : 0 <= x -> 0 <= y -> (x + y != 0) = (x != 0) || (y != 0).
  Proof.
    move=> Hx Hy.
    rewrite -negb_and.
    apply/idP/idP => /eqP H.
    - apply/negP => Hc.
      apply: H.
      apply/eqP.
      rewrite paddr_eq0 //=.
    - apply/negP => Hc.
      move/eqP in H.
      move/negP in H.
      apply: H.
      rewrite -paddr_eq0 //=.
  Qed.
  
  Lemma test8 (a b : R) : 0 < a -> 0 <= b -> a + b != 0.
  Proof.
    rewrite lt0r.
    case/andP => H0 Ha Hb.
    rewrite paddr_eq0' //=.
    by apply/orP/or_introl.
  Qed.
  
  Lemma test6 (a b : R) : 0 < a -> 0 <= b -> 0 < a + b.
  Proof.
    move=> Ha Hb.
    rewrite lt0r.
    apply/andP.
    split.
    - by apply: test8.
    - have H : 0 < a -> 0 <= a.
      {
        rewrite lt0r.
        by case/andP.
      }.
      move/H in Ha.
      by apply: addr_ge0.
  Qed.
  
  Lemma test7 (a : R) : a <> 0 -> 0 < a ^+2.
  Proof.
    move/eqP.
    by rewrite exprn_even_gt0.
  Qed.
  
  Lemma test5 (x1 x2 : R) : x1 <> 0 -> 0 < x1 ^+ 2 + ((x1 + x2) ^+ 2 + x2 ^+ 2).
  Proof.
    move=> H.
    Search (0 <= _).
    Check mulr_ge0 : forall (R : numDomainType) (x y : R), 0 <= x -> 0 <= y -> 0 <= x * y.
    apply: test6; [| apply: addr_ge0].
    - exact: test7.
    - exact: sqr_ge0.
    - exact: sqr_ge0.
  Qed.
  
  Goal injective (fun (x : R) => x ^+ 3).
  Proof.
    have Hab a b : (a * b == 0) = (a == 0) || (b == 0) by admit.
    (* Mathcomp では、integral domain でないと成り立たないか。 *)

    move=> x1 x2 H.
    have : (x1 - x2) * (x1 ^+ 2 + x1 * x2 + x2 ^+ 2) = 0 by rewrite test3 H; ring.
    
    move/eqP.
    rewrite Hab.
    case/orP => /eqP.
    - by move/subr0_eq.
    - case Ha1 : (x1 == 0); move/eqP in Ha1.
      + rewrite Ha1 expr0n /= add0r mul0r add0r.
        move/eqP.
        by rewrite expf_eq0 => /andP [] _ /eqP.
        
      + have H3 : x1 ^+ 2 + ((x1 + x2) ^+ 2 + x2 ^+ 2) > 0 by apply: test5.
        (* 二乗和に x1 は 非零 *)
        have H4 : 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) > 0 by rewrite test4 H3.
        have H5 : x1 ^ 2 + x1 * x2 + x2 ^ 2 > 0 by rewrite -(pmulr_rgt0 (x:=2)).
        move=> H6.
        move: H5.
        rewrite H6.
        Check test2 0.
        by rewrite test2.
  Admitted.
*)  
End Functions.

(* END *)
