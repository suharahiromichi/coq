(**
コンピュータの数学 2.6 離散系および連続系の微積分学（和差分学)
======

自然数での下降階乗冪と上昇階乗冪の和分差分の計算 ffact, rfact

2022_08_28 @suharahiromichi
*)
From mathcomp Require Import all_ssreflect.
From common Require Import ssrsumop ssromega.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
# 和分差分学の定義と補題
 *)
Section FINCAL.
(**
## 短調増加
*)
  Definition monotone f := forall (x : nat), f x <= f x.+1.

(**
## 差分 difference 
*)
  Definition diff f := fun x => f x.+1 - f x.

(**
### 差分の公式
 *)
  Lemma diff_split f g (x : nat) :
    monotone f -> monotone g ->
    diff f x + diff g x = diff (fun x => f x + g x) x.
  Proof.
    move=> Hf Hg.
    rewrite /diff.
    rewrite addnBA; last done.
    rewrite subnDA.
    rewrite addnBAC; last done.
    done.
  Qed.

  Lemma diff_distr c f (x : nat) :
    c * diff f x = diff (fun x => c * f x) x.
  Proof.
    rewrite /diff.
    by rewrite mulnBr.
  Qed.

(**
## 和分 summation

### 和分の定義

```Σa,b g(k)δk = Σ(a <= k < b)g(k)```
 *)
  Definition summ g a b := \sum_(a <= k < b)(g k).
  
(**
### 差分と和分の関係
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
一般に成立するはずの関係
*) 
  Lemma summ_diff f a b : a <= b -> summ (diff f) a b = f b - f a.
  Proof.
    rewrite /summ /diff.
  Admitted.                                 (* 途中！ *)

(**
### 和分の公式
 *)
  Lemma summ_nil f a :  summ f a a = 0.
  Proof.
    rewrite /summ.
    by rewrite sum_nil.
  Qed.
  
  Lemma summ_split f g a b :
    a <= b ->
    summ f a b + summ g a b = summ (fun k => f k + g k) a b.
  Proof.
    rewrite leq_eqVlt => /orP [Heq | Hlt].
    - move/eqP in Heq.                      (* a = b の場合 *)
      rewrite -Heq.
      by rewrite 3!summ_nil.
    - rewrite /summ.                        (* a < b の場合 *)
      by apply: sum_split.
  Qed.

  Lemma summ_distr c f a b :
    a <= b -> c * summ f a b = summ (fun k => c * f k) a b.
  Proof.
    rewrite leq_eqVlt => /orP [Heq | Hlt].
    - move/eqP in Heq.                      (* a = b の場合 *)
      rewrite -Heq.
      by rewrite 2!summ_nil muln0.
    - by rewrite /summ sum_distrr.
  Qed.

(**
## 一般化した関数拡張の公理

関数の部分だけを取り出して関数拡張する場合、Standard Coq の
functional_extensionality を使うのではだめで、
引数xが m≦x である条件を追加する必要がある。
*)
(*  
  Axiom functional_extensionality_ge_m : 
    forall (m : nat) (f g : nat -> nat),
      (forall x : nat, m <= x -> f x = g x) -> f = g.
*)
  Axiom functional_extensionality' : 
    forall (A B : Type) (P : A -> Prop) (f g : A -> B),
      (forall (x : A), P x -> f x = g x) -> f = g.
  Check fun (m : nat) => @functional_extensionality' nat nat (leq m).

End FINCAL.
  
(**
# 下降階乗冪 ffact, falling_factorial
 *)
Section FFACT.
(**
## 補題
 *)
  Check ffactn0 : forall n : nat, n ^_ 0 = 1.
  Check ffact0n : forall m : nat, 0 ^_ m = (m == 0).
  Check ffactn1 : forall n : nat, n ^_ 1 = n.
  
(**
x^_m が x に対して単調に増加することの証明
*)
  Lemma ffact_monotone m : monotone (fun x => x ^_ m).
  Proof.
    move=> x.
    case: m => // m.                        (* m = 0 の場合を片付ける。 *)
    rewrite ffactSS ffactnSr.               (* m ≧ 1 の場合 *)
    rewrite mulnC leq_mul2r.
    apply/orP/or_intror.
    by ssromega.
  Qed.
  
(**
## 下降階乗冪の差分

```Δx^_(m + 1) / Δx = (m + 1) * x^_m```
*)  
  Lemma diff_ffactE' (m : nat) (x : nat) :
    m <= x -> diff (fun x => x^_m.+1) x = m.+1 * x^_m.
  Proof.
    move=> Hmx.
(*
diff (falling_factorial^~ m.+1) x = m.+1 * x ^_ m
*)
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
より直感的かかたち：

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
特殊なかたち；

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
  
(**
## 下降階乗冪の和分

下降階乗冪の和分（0から）

bigopの関数部分をcongrで取り出し、一般化した関数拡張の公理を使用して証明する。
*)
  Lemma summ_ffactE' (m : nat) (b : nat) :
    1 <= m -> m <= b -> summ (fun x => m.+1 * x^_m) 0 b = b^_m.+1.
  Proof.
    move=> Hm.                         (* 0^_1 = 1 を回避するため。 *)
    move=> Hmb.
    rewrite -[RHS](@summ_diff' (fun x => x^_m.+1)) //.
    - congr (summ _ 0 b).
      apply: (@functional_extensionality' _ _ (leq m)) => x Hmx.
      by rewrite diff_ffactE'.
    - move=> x.
      by apply: ffact_monotone.
  Qed.
  
(**
## 下降階乗冪の和分（任意のaから）
*)  
  Lemma summ_ffactE (m : nat) (a b : nat) :
    a <= b -> m < a -> summ (fun x => x * x^_m) a b = b^_m.+1.
  Proof.
  Admitted.                                 (* 途中！ *)

End FFACT.

(**
# 上昇階乗冪 rfact, rising_factorial
 *)
Section RFACT.

  Fixpoint rfact_rec n m := if m is m'.+1 then n * rfact_rec n.+1 m' else 1.
  Definition rising_factorial := nosimpl rfact_rec.

  Notation "n ^^ m" := (rising_factorial n m)
                         (at level 30, right associativity).

  Lemma rfactn0 n : n ^^ 0 = 1. Proof. by []. Qed.

  Lemma rfact0n m : 0 ^^ m = (m == 0). Proof. by case: m. Qed.

  Lemma rfactnS n m : n ^^ m.+1 = n * n.+1 ^^ m. Proof. by []. Qed.

  Lemma rfactn1 n : n ^^ 1 = n. Proof. exact: muln1. Qed.

  Lemma rfactSS n m : n.+1 ^^ m.+1 = n.+1 ^^ m * (n + m.+1).
  Proof.
  Admitted.

  Lemma rfactnSr n m : n ^^ m.+1 = n * n.+1 ^^m.
  Proof.
  Admitted.
  
(**
x^^m が x に対して単調に増加することの証明
*)
  Lemma rfact_monotone m : monotone (fun x => x ^^ m).
  Proof.
    move=> x.
    case: m => // m.                        (* m = 0 の場合を片付ける。 *)
    rewrite rfactSS rfactnSr.               (* m ≧ 1 の場合 *)
(*
x ^_ m * (x - m) <= x.+1 * x ^_ m
*)
    rewrite mulnDr mulnC.
    by rewrite leq_addr.
  Qed.
  
(**
## 上昇階乗冪の差分

```Δx^^(m + 1) / Δx = (m + 1) * (x + 1)^^m```
*)  
  Lemma diff_rfactE' (m : nat) (x : nat) :
    m <= x -> diff (fun x => x^^m.+1) x = m.+1 * x.+1^^m.
  Proof.
    move=> Hmx.
    rewrite /diff.
    rewrite rfactSS rfactnSr.
    rewrite [x.+1 ^^ m * (x + m.+1)]mulnC.
    rewrite mulnDl addnC -addnBA //=.
    by rewrite subnn addn0.
  Qed.
  
(**
より直感的かかたち：

```Δx^^m / Δx = m * (x + 1)^^(m - 1)```
*)  
  Lemma diff_rfactE (m : nat) (x : nat) :
    0 < m -> m <= x -> diff (fun x => x^^m) x = m * x.+1^^m.-1.
  Proof.
    case: m => //=.
    move=> m H0m Hmx.
    rewrite diff_rfactE' //.
    by ssromega.
  Qed.
  
(**
特殊なかたち；

```Δx/Δx = 1```
*)  
  Check @diff_rfactE' 0
    : forall x : nat, 0 <= x -> diff (fun x => x^^1) x = 1 * x^^0.

  Lemma diff_idE' (x : nat) : diff id x = 1.
  Proof.
    rewrite -[RHS](rfactn0 x) -[RHS]mul1n.
    rewrite -(@diff_rfactE' 0 x); last done.
    rewrite /rising_factorial /rfact_rec.
    rewrite /diff.
    by ssromega.
  Qed.
  
(**
## 上昇階乗冪の和分

上昇階乗冪の和分（0から）

bigopの関数部分をcongrで取り出し、一般化した関数拡張の公理を使用して証明する。
*)
  Lemma summ_rfactE' (m : nat) (b : nat) :
    1 <= m -> m <= b -> summ (fun x => m.+1 * x.+1^^m) 0 b = b^^m.+1.
  Proof.
    move=> Hm.                         (* 0^^1 = 1 を回避するため。 *)
    move=> Hmb.
    Check (@summ_diff' (fun x => x^^m)).
    rewrite -[RHS](@summ_diff' (fun x => x^^m.+1)) //.
    - congr (summ _ 0 b).
      apply: (@functional_extensionality' _ _ (leq m)) => x Hmx.
      by rewrite diff_rfactE'.
    - move=> x.
      by apply: rfact_monotone.
  Qed.
  
(**
## 上昇階乗冪の和分（任意のaから）
*)  
  Lemma summ_rfactE (m : nat) (a b : nat) :
    a <= b -> m < a -> summ (fun k => k * k^^m) a b = b^^m.+1.
  Proof.
  Admitted.                                 (* 途中！ *)

End RFACT.

(* END *)
