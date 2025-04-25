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
  Check @lt_eqF
    : forall (disp : order.Order.disp_t) (T : porderType disp) (x y : T), (x < y)%O -> (x == y) = false.
  Check @gt_eqF
    : forall (disp : order.Order.disp_t) (T : porderType disp) (x y : T), (y < x)%O -> (x == y) = false.
  
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

  Goal 3 != 0 :> R.
  Proof.
    by apply: ne_of_gt.                     (* 0 < 3  *)
  Qed.
  
End Sample.


Section Functions.
  
  (* ここで使う実数型 R *)
  Variable R : rcfType.                 (* Real Closed Field 実閉体 *)
  (* MathComp-analysis の realType は rcf である。 *)
  
(**
## 8.1.2. Definition

単射
*)
  Print injective.
  Check fun (rT aT : Type) (f : aT -> rT) => (forall x1 x2 : aT, f x1 = f x2 -> x1 = x2).
  
(**
## 8.1.3. Example
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

(**
## 8.1.4. Example
*)
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
## 8.1.5. Definition

全射
*)
  Definition surjective (rT aT : Type) (f : aT -> rT) := forall y, exists x, f x = y.
  
(**
## 8.1.6. Example
*)
  Goal surjective (fun (a : rat) => 3 * a + 2).
  Proof.
    rewrite /surjective => y.
    exists ((y - 2) / 3).
    have -> (a : rat) : 3 * (a / 3) = a
      by rewrite mulrA [3 * a]mulrC -mulrA divff; first rewrite mulr1.
    ring.
  Qed.
  
(**
## 8.1.7. Example
*)
  Goal ~ surjective  (fun x : R => x^+2).
  Proof.
    rewrite /surjective.
    move/(_ (- 1)).                         (* 届かない値 *)
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
## 8.1.8. Example

Musketeer type 三銃士型
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
  
(**
## 8.1.9. Example
*)
  Goal ~ surjective f.
  Proof.
    rewrite /surjective.
    case/(_ porthos).        (* 前提のexists x を forall x にする。 *)
    by case.                 (* x を三つの要素で場合分けする。  *)
    (* どれも = porthos にならない。 *)
  Qed.

(**
## 8.1.10. Example
*)
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

(**
## 8.1.11. Example
*)
  Goal surjective g.
  Proof.
    case.
    - exists aramis => //=.
    - exists athos => //=.
    - exists porthos => //=.
  Qed.
  
(**
## 8.1.12. Example

``x |-> x^3`` は単射である。
*)
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
    rewrite GRing.mulf_eq0.                 (* fieldで成立する。 *)
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
## 8.1.13 Exercise

### 8.1.13. Exercises 1.
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

(**
### 8.1.13. Exercises 2.
*)  
  Goal ~ injective (fun (x : R) => (3 : R)).
  Proof.
    Check 3 = 3 -> 0 = 3 -> False.
    have H : 3 = 3 :> R by ring.
    move/(_ 0 3 H)/eqP.
    have -> : (0 == 3 :> R) = false by apply: lt_eqF.
    done.
  Qed.
  
(**
### 8.1.13. Exercises 3.

有理数の場合
*)
  Goal injective (fun (x : rat) => 3 * x - 1).
  Proof.
    move=> x1 x2.
    have Hinv (x y : rat) : x = y -> (x + 1) / 3 = (y + 1) / 3 by move=> ->.
    move/Hinv.
    rewrite -2!addrA.
    have -> : -1 + 1 = 0 :> rat by ring.
    rewrite 2!addr0 2![3 * _]mulrC -2!mulrA.
    have -> : 3 / 3 = 1 :> rat by rewrite mulrC; apply: mulVq.
    by rewrite 2!mulr1.
  Qed.

(**
### 8.1.13. Exercises 4.

整数の場合は、単射の合成でも、逆関数でもできるが、そもそも、lia で解ける。
*)
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

(**
### 8.1.13. Exercises 5.
*)
  Goal surjective (fun (x : R) => 3 * x).
  Proof.
    move=> y.
    exists (y / 3).
    rewrite mulrC -mulrA mulVf.
    - by rewrite mulr1.
    - exact: ne_of_gt.                      (* 0 < 3 *)
  Qed.

(**
### 8.1.13. Exercises 6.
*)
  Goal ~ surjective (fun (x : int) => 3 * x).
  Proof.
    move/(_ 2).
    case=> x.
    lia.
  Qed.

(**
### 8.1.13. Exercises 7.

自然数の場合。素数と合成数から矛盾を導く。
*)
  Lemma not_prime (m : nat) : (2 <= m)%N -> ~~ prime (m * m).
  Proof.
    move=> Hm.
    apply/primePn/or_intror.
    exists m.
    - apply/andP.
      by split; [lia | apply: ltn_Pmull; lia].
    - by apply: dvdn_mulr.
  Qed.

  Goal ~ surjective (fun (n : nat) => (n ^ 2)%N).
  Proof.
    move/(_ 3%N).
    case=> n.
    case: n => //= n.                       (* n.+1, n >= 1 *)
    case: n => //= n.                       (* n.+2, n >= 2 *)
    have H x y : x = y -> prime x = prime y by move=> ->.
    move/H.
    (* 右辺、素数 *)
    have -> : prime 3 by done.
    (* 左辺、合成数 *)
    have Hp m : ~~ prime (m.+2 ^ 2)%N by rewrite -mulnn; apply: not_prime.
    move/(_ n) : Hp.
    move/negbTE => ->.
    (* false = true *)
    done.
  Qed.

(**
### 8.1.13. Exercises 8.
 *)
  Inductive White :=
  | meg
  | jack.

  Definition h (x : Musketeer) : White :=
    match x with
    | athos => jack
    | porthos => meg
    | aramis => jack
    end.

  Goal ~ injective h.
  Proof.
    by move/(_ athos aramis)/(_ erefl).
  Qed.
  
(**
### 8.1.13. Exercises 9.
 *)
  Goal surjective h.
  Proof.
    case.
    - exists porthos => //=.
    - exists athos => //=.
  Qed.

(**
### 8.1.13. Exercises 10.
 *)
  Definition l (x : White) : Musketeer :=
    match x with
    | meg => aramis
    | jack => porthos
    end.
  (* athos に行かない。 *)

  Goal injective l.
  Proof.
    by case; case.
  Qed.
  
(**
### 8.1.13. Exercises 11.
 *)
  Goal ~ surjective l.
  Proof.
    case/(_ athos).                         (* 前提のexists x を forall x にする。 *)
    by case.                                (* x で場合分けする。 *)
  Qed.

(**
### 8.1.13. Exercises 12.
 *)
  Goal forall (X Y : Type) (f : X -> Y), injective f <-> forall (x1 x2 : X), x1 <> x2 -> f x1 <> f x2.
  Proof.
    move=> X Y f.
    split=> H x1 x2.
    - by auto.
    - move: (H x1 x2).
      Check contraPP : forall Q P : Prop, (~ Q -> ~ P) -> P -> Q. (* 二重否定除去を使う。 *)
      by move/contraPP.
  Qed.

(**
### 8.1.13. Exercises 13.
 *)
  Lemma addq_inj a : injective (fun (x : rat) => x + a).
  Proof.
    move=> x1 x2.
    have H x y : x = y -> x - a = y - a by move=> ->.
    move/H.
    rewrite -2!addrA.
    have -> : a - a = 0 by ring.
    by rewrite 2!addr0.
  Qed.
  
  Goal forall (f : rat -> rat), (injective f -> injective (fun x => f x + 1)).
  Proof.
    move=> f Hf x1 x2 H.
    apply: Hf.
    by apply: (@addq_inj 1).
  Qed.
  
(**
### 8.1.13. Exercises 14.
 *)
  Section e14.
(**
``f(x) = - x`` のとき、``f(1) + 1 = f(2) + 2 = 0`` という反例を示す。
*)
    Let f (x : rat) : rat := - x.
    
(**
   f(x) = -x は単射である。
*)
    Lemma injective_f : injective f.
    Proof.
      done.
    Qed.
    
    Goal ~ forall (f : rat -> rat), injective f -> injective (fun x => f x + x).
    Proof.
      move/(_ f injective_f).
      rewrite /injective.
      have Hcontra : (fun x => - x + x) 1%:Q = (fun x => - x + x) 2%:Q by done.
      move/(_ 1 2 Hcontra).
      done.
    Qed.
  End e14.

(**
### 8.1.13. Exercises 15.
 *)
  Goal forall (f : int -> int), (~ surjective f -> ~ surjective (fun x => 2 * f x)).
  Proof.
    move=> f.
    apply/contra_not.
    move=> /= Hc y.
    case: (Hc (2 * y)) => x {Hc} Hc'.
    exists x.
    lia.
  Qed.
  
(**
### 8.1.13. Exercises 16.

``c != 0`` の条件が必要であろう。
 *)
  Goal forall (c : R), c != 0 -> surjective (fun (x : R) => c * x).
  Proof.
    move=> c Hc y.
    exists (y / c).
    rewrite mulrC -mulrA mulVf //=.
    by rewrite mulr1.
  Qed.

(**
### 8.1.13. Exercises 17.

f は、狭義単調増加、ならば単射。
 *)
  Lemma lt_trichotomy (x y : rat) : x < y \/ x = y \/ x > y. (* 問題文は誤記 *)
  Proof.
    case: ltgtP => H.                       (* Order.v *)
    - by apply/or_introl.
    - by apply/or_intror/or_intror.
    - by apply/or_intror/or_introl.
  Qed.
  
  (* injective の対偶 *)
  Lemma contra_injective (f : rat -> rat) :
    (forall (x1 x2 : rat), x1 != x2 -> f x1 != f x2) -> injective f.
  Proof.
    move=> Hc x1 x2.
    move: (Hc x1 x2) => {Hc} /contra.
    rewrite 2!negbK.
    move=> Hc /eqP H.
    apply/eqP.
    by auto.
  Qed.
  
  Goal forall (f : rat -> rat), (forall x y, x < y -> f x < f y) -> injective f.
  Proof.
    move=> f Hxy.
    apply: contra_injective => x1 x2.
    case: (lt_trichotomy x1 x2) => [|[]].
    (* x1 < x2 *)
    - move=> Hc _.
      by move: Hc => /Hxy/lt_eqF ->.
    (* x1 = x2 *)
    - by move/eqP => ->.                    (* 前提矛盾 *)
    (* x2 > x1 *)
    - move=> Hc _.
      by move: Hc => /Hxy/gt_eqF ->.
  Qed.
    
(**
### 8.1.13. Exercises 18.
 *)
  Goal forall (X : Type) (f : X -> nat) (x0 : X) (i : X -> X),
      f x0 = 0 -> (forall (x : X), f (i x) = (f x).+1) -> surjective f.
  Proof.
    move=> X f x0 i Hf H.
    elim=> [| y [x IHy]].  (* ついでに IHy の exists x を取り出す。 *)
    - exists x0 => //.
    - exists (i x).
      rewrite H.
      by congr (_ .+1).
  Qed.
  
End Functions.

(* END *)
