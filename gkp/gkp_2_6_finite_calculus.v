(**
和分差分
======

2021_02_20 @suharahiromichi

*)
From mathcomp Require Import all_ssreflect.
Require Import ssrsumop ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

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
    0 < m ->  m < x -> diff (fun x => x^_m) x = m * x^_m.-1.
  Proof.
    move=> H0m Hmx.
    have H : m.-1.+1 = m by rewrite prednK.
    rewrite -H -pred_Sn.
    rewrite diff_ffactE' //.
      by ssromega.
  Qed.


  Lemma ffact0 x : x^_0 = 1.
  Proof. done. Qed.
  
  Lemma ffact1 x : x^_1 = x.                (* notu *)
  Proof.
    rewrite /falling_factorial /ffact_rec.
      by rewrite muln1.
  Qed.
  
  Lemma id_muln1 x : id x = muln^~ 1 x.     (* notu *)
  Proof. by rewrite /= muln1. Qed.
  
(**
## 特殊なかたち；

```Δx/Δx = 1```
*)  
  Check @diff_ffactE' 0
    : forall x : nat, 0 <= x -> diff (fun x => x^_1) x = 1 * x^_0.

  Lemma diff_idE (x : nat) : diff id x = 1.
  Proof.
    rewrite -[RHS](ffact0 x) -[RHS]mul1n.
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
  Lemma subn_eq0' n : n - n = 0.            (* notu *)
  Proof.
    have Heq x : x - x = 0 by apply/eqP; rewrite subn_eq0.
      by rewrite Heq.
  Qed.
  
  Lemma summ_diff f a b : a <= b -> summ (diff f) a b = f b - f a.
  Proof.
    rewrite /summ /diff.
  Admitted.

(**
## 下降階乗冪の和分
*)


End Summation.

(* END *)
