(**
和分差分
======

2021_02_20 @suharahiromichi

*)
From mathcomp Require Import all_ssreflect.
Require Import ssrsumop ssromega.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
# 補題
 *)

  Check ffactn0 : forall n : nat, n ^_ 0 = 1.
  Check ffact0n : forall m : nat, 0 ^_ m = (m == 0).
  Check ffactn1 : forall n : nat, n ^_ 1 = n.
  
  Lemma ffact0n' m : 1 <= m -> 0^_m = 0.
  Proof.
      by apply: ffact_small.
  Qed.
  
  Lemma id_muln1 x : id x = muln^~ 1 x.     (* notu *)
  Proof. by rewrite /= muln1. Qed.
  
  Lemma subn_eq0' n : n - n = 0.            (* notu *)
  Proof.
    have Heq x : x - x = 0 by apply/eqP; rewrite subn_eq0.
      by rewrite Heq.
  Qed.

(**
## x^_m が x に対して単調に増加することの証明
*)
  Lemma ffact_monotone x m : x ^_ m.+1 <= x.+1 ^_ m.+1.
  Proof.
    rewrite ffactSS ffactnSr.
    rewrite mulnC leq_mul2r.
    apply/orP/or_intror.
      by ssromega.
  Qed.
  
(**
# 下降階乗冪の差分
*)

Section Difference.

(**
## 差分 difference の定義
*)  
  Definition diff f := fun x => f x.+1 - f x.

(**
## 証明しやすいかたち：

```Δx^_(m + 1) / Δx = (m + 1) * x^_m```
*)  
  Lemma diff_ffactE' (m : nat) (x : nat) :
    m <= x -> diff (fun x => x^_m.+1) x = m.+1 * x^_m.
  Proof.
    move=> Hmx.
    rewrite /diff.
    rewrite ffactSS ffactnSr [x^_m * (x - m)]mulnC.
    rewrite mulnBl mulSnr.
    rewrite subnBA; last by rewrite leq_mul.
    rewrite -[x * x^_m + x^_m + m * x^_m]addnA.
    rewrite -{2}[x * x^_m]addn0 subnDl subn0.
    rewrite -mulSn.
    done.
  Qed.
  
(**
## より直感的かかたち：

```Δx^_m / Δx = m * x^_(m - 1)```
*)  
  Lemma diff_ffactE (m : nat) (x : nat) :
    0 < m -> m <= x -> diff (fun x => x^_m) x = m * x^_m.-1.
  Proof.
    move=> H0m Hmx.
    have H : m.-1.+1 = m by rewrite prednK.
    rewrite -H -pred_Sn.
    rewrite diff_ffactE' //.
      by ssromega.
  Qed.
  
(**
## 特殊なかたち；

```Δx/Δx = 1```
*)  
  Check @diff_ffactE' 0
    : forall x : nat, 0 <= x -> diff (fun x => x^_1) x = 1 * x^_0.

  Lemma diff_idE (x : nat) : diff id x = 1.
  Proof.
    rewrite -[RHS](ffactn0 x) -[RHS]mul1n.
    rewrite -(@diff_ffactE' 0 x); last done.
    rewrite /falling_factorial /ffact_rec.
    rewrite /diff.
      by ssromega.
  Qed.
  
End Difference.

(**
# 下降階乗冪の和分
 *)
Section Summation.

(**
## 和分の定義

```Σa,b g(k)δk = Σ(a <= k < b)g(k)```
 *)
  Definition summ g a b := \sum_(a <= k < b)(g k).
  
(**
## 差分と和分の関係

### 特別なかたち （下降階乗冪で成立する）
*) 
  Lemma summ_diff' f b : f 0 = 0 ->
                         (forall n, f n <= f n.+1) ->
                         summ (diff f) 0 b = f b.
  Proof.
    move=> Hf0 Hfn.
    rewrite /summ /diff.
    elim: b.
    - rewrite sum_nil'.
        by rewrite Hf0.
    - move=> n IHn.
      rewrite sum_last; last done.
      rewrite IHn.
        by rewrite subnKC.
  Qed.
  
(**
### 一般に成立するはずの関係
*) 
  Lemma summ_diff f a b : a <= b -> summ (diff f) a b = f b - f a.
  Proof.
    rewrite /summ /diff.
  Admitted.                                 (* 途中！ *)

(**
## 下降階乗冪の和分（0から）
*)
(**
関数の部分だけを取り出して、関数拡張してもだめである。
*)
  Goal forall m b,
      summ (fun k : nat => m.+1 * k ^_ m) 0 b =
      summ (diff (falling_factorial^~ m.+1)) 0 b.
  Proof.
    move=> m b.
    congr (summ _ 0 b).
    apply: functional_extensionality => k.
    rewrite diff_ffactE' //.
    (* 関数拡張では、m と k  の間の条件が解消できないので、だめである。 *)
  Admitted.                                 (* OK！ *)
  
  Lemma l_summ_ffactE m b : m <= b ->
                            summ (fun k : nat => m.+1 * k ^_ m) 0 b =
                            summ (diff (falling_factorial^~ m.+1)) 0 b.
  Proof.
    rewrite /summ.
    elim: b => [| b IHb Hmb].
    - by rewrite 2!sum_nil'.
    - rewrite sum_last; last done.
      rewrite sum_last; last done.
      congr (_ + _).
      + apply: IHb.
        admit.                              (* m <= b *)
      + rewrite diff_ffactE' //.
        admit.                              (* m <= b *)
  Admitted.
  
  Lemma summ_ffactE' (m : nat) (b : nat) :
    1 <= m -> m <= b -> summ (fun k => m.+1 * k^_m) 0 b = b^_m.+1.
  Proof.
    move=> Hm.                              (* 0^_1 = 1 を回避するため。 *)
    move=> Hmb.
    rewrite -[RHS](@summ_diff' (fun k => k^_m.+1)) //.
    - by apply: l_summ_ffactE.
    - move=> x.
        by apply: ffact_monotone.
  Qed.
  
(**
## 下降階乗冪の和分（任意のaから）
*)  
  Lemma summ_ffactE (m : nat) (a b : nat) :
    a <= b -> m < a -> summ (fun k => k * k^_m) a b = b^_m.+1.
  Proof.
  Admitted.                                 (* 途中！ *)

End Summation.

(* END *)



  Goal forall (s1 s2 : pred T), predI s1 s2 = predI s2 s1.
  Proof.
    move=> s1 s2.
    rewrite /predI.
    rewrite /SimplPred.
    f_equal.



