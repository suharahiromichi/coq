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
  Definition monotone a := forall (x : nat), a x <= a x.+1.

(**
## 差分 difference 

````
diff b = diff (fun x => b x) = Δb x / Δx = a x
```
を求める。連続系とのアナロジーでは、b は a の原始関数となる。
*)
  Definition diff b := fun x => b x.+1 - b x. (* = a *)

(**
### 差分の公式
 *)
  Lemma diff_split a b (x : nat) :
    monotone a -> monotone b ->
    diff a x + diff b x = diff (fun x => a x + b x) x.
  Proof.
    move=> Ha Hb.
    rewrite /diff.
    rewrite addnBA; last done.
    rewrite subnDA.
    rewrite addnBAC; last done.
    done.
  Qed.

  Lemma diff_distr c b (x : nat) :
    c * diff b x = diff (fun x => c * b x) x.
  Proof.
    rewrite /diff.
    by rewrite mulnBr.
  Qed.

(**
## 和分 summation

### 和分の定義

```Σb(x)δx = Σ(n1 <= k < n2) b(x)```
 *)
  Definition summ b n1 n2 := \sum_(n1 <= x < n2)(b x).

(**
### 差分と和分の関係
*) 
(**
差分・和分の基本公式 : 微積分の基本公式のアナロジー (by mh)

Σ a を計算することは a n = b n+1 - b n となる数列 b が既知であれば, 
b の差を求めることである。

積分計算とのアナロジーで b を a の原始関数と言ってもよいでしょう ...
```
F'(x) = f(x) のとき ∫ f(x)dx = F(x_max) - F(x_min)
```

総和の場合は、(``diff b = a``)
```
b n+1 - b n = a n のとき Σa = b n+1 - b 0
```
*)
  Lemma summ_diff' b m : b 0 = 0 ->
                         (forall n, b n <= b n.+1) ->
                         summ (diff b) 0 m = b m.
  Proof.
    move=> Hf0 Hfn.
    rewrite /summ /diff.
    elim: m.
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
  Lemma summ_diff b n1 n2 : n1 <= n2 -> summ (diff b) n1 n2 = b n2 - b n1.
  Proof.
    rewrite /summ /diff.
  Admitted.                                 (* 途中！ *)

(**
### 和分の公式
 *)
  Lemma summ_nil a n :  summ a n n = 0.
  Proof.
    rewrite /summ.
    by rewrite sum_nil.
  Qed.
  
  Lemma summ_split a b n1 n2 :
    n1 <= n2 ->
    summ a n1 n2 + summ b n1 n2 = summ (fun x => a x + b x) n1 n2.
  Proof.
    rewrite leq_eqVlt => /orP [Heq | Hlt].
    - move/eqP in Heq.                      (* n1 = n2 の場合 *)
      rewrite -Heq.
      by rewrite 3!summ_nil.
    - rewrite /summ.                        (* n1 < n2 の場合 *)
      by apply: sum_split.
  Qed.

  Lemma summ_distr c a n1 n2 :
    n1 <= n2 -> c * summ a n1 n2 = summ (fun x => c * a x) n1 n2.
  Proof.
    rewrite leq_eqVlt => /orP [Heq | Hlt].
    - move/eqP in Heq.                      (* n1 = n2 の場合 *)
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
    forall (A B : Type) (P : A -> Prop) (a b : A -> B),
      (forall (x : A), P x -> a x = b x) -> a = b.
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
  Check ffactn1 : forall n : nat, n ^_ 1 = n.
  Check ffact0n : forall m : nat, 0 ^_ m = (m == 0).
  Lemma  ffact0n' m : 0 < m ->  0 ^_ m = 0.
  Proof. by case: m. Qed.
  
(**
x^_m が x に対して単調に増加することの証明

``monotone (falling_factorial^~ m)`` という記法は使わないことにします。
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
``->`` の右のxを抽象して ``=1`` のかたちにすると、
``m <= x``の条件が無視されるため、あとで適用したときに証明が進まなくなる。
*)
  
(**
より直感的かかたち：

```Δx^_m / Δx = m * x^_(m - 1)```
*)  
  Lemma diff_ffactE (m : nat) (x : nat) :
    0 < m -> m <= x -> diff (fun x => x^_m) x = m * x^_m.-1.
  (*                         b                  a *)
  Proof.
    case: m => //=.
    move=> m H0m Hmx.
    rewrite diff_ffactE' //.
    by ssromega.
  Qed.
  
(**
## 下降階乗冪の和分

下降階乗冪の和分（0から）
x*)
  Lemma summ_ffactE' (m : nat) (n : nat) :
    1 <= m -> m <= n -> summ (fun x => m * x^_m.-1) 0 n = n^_m.
  (*                          a *)
  Proof.
    move=> Hm.                         (* 0^^1 = 1 を回避するため。 *)
    move=> Hmn.
    rewrite -[RHS](@summ_diff' (fun x => x^_m)) //.
    (*                          b *)
    - congr (summ _ 0 n).
      apply: (@functional_extensionality' _ _ (leq m)) => x Hmx.
      by rewrite diff_ffactE.
    - by apply: ffact0n'.
    - move=> x.
      by apply: ffact_monotone.
  Qed.
(**
bigopの関数部分をcongrで取り出し、一般化した関数拡張の公理を使用して証明する。
*)
  
(**
下降階乗冪の和分（任意のaから）
*)  
  Lemma summ_ffactE (m : nat) (n1 n2 : nat) :
    n1 <= n2 -> m < n1 -> summ (fun x => x * x^_m) n1 n2 = n2^_m.+1.
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
  Lemma rfactnS n m : n ^^ m.+1 = n * n.+1 ^^ m. Proof. by []. Qed.
  Lemma rfact0n m : 0 ^^ m = (m == 0). Proof. by case: m. Qed.
  Lemma rfact0n' m : 0 < m -> 0 ^^ m = 0. Proof. by case: m. Qed.
  
  Lemma rfactn1 n : n ^^ 1 = n. Proof. exact: muln1. Qed.

  Lemma rfactnSr n m : n ^^ m.+1 = n^^m * (n + m).
  Proof.
    elim: n m => [|n IHn] [|m] //=.
    - rewrite rfactn1 rfactn0.
      by ssromega.
  Admitted.                                 (* XXXX *)
  
  Lemma rfactSS n m : n.+1 ^^ m.+1 = n.+1 ^^ m * (n + m.+1).
  Proof.
    rewrite rfactnSr.
    by rewrite addSnnS.
  Qed.
  
(**
x^^m が x に対して単調に増加することの証明
*)
  Lemma rfact_monotone m : monotone (fun x => x ^^ m).
  Proof.
    move=> x.
    case: m => // m.                        (* m = 0 の場合を片付ける。 *)
    rewrite rfactSS rfactnS.                (* m ≧ 1 の場合 *)
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
    rewrite rfactSS rfactnS.
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
  (*                         b                  a *)
  Proof.
    case: m => //=.
    move=> m H0m Hmx.
    rewrite diff_rfactE' //.
    by ssromega.
  Qed.
  
(**
## 上昇階乗冪の和分

上昇階乗冪の和分（0から）
*)
  Lemma summ_rfactE' (m : nat) (n : nat) :
    1 <= m -> m <= n -> summ (fun x => m * x.+1^^m.-1) 0 n = n^^m.
  (*                          a *)
  Proof.
    move=> Hm.                         (* 0^^1 = 1 を回避するため。 *)
    move=> Hmn.
    Check (@summ_diff (fun x => x^^m)).
    rewrite -[RHS](@summ_diff' (fun x => x^^m)) //.
    (*                          b *)
    - congr (summ _ 0 n).
      apply: (@functional_extensionality' _ _ (leq m)) => x Hmx.
      by rewrite diff_rfactE.
    - by apply: rfact0n'.
    - move=> x.
      by apply: rfact_monotone.
  Qed.
  
(**
上昇階乗冪の和分（任意のaから）
*)  
  Lemma summ_rfactE (m : nat) (n1 n2 : nat) :
    n1 <= n2 -> m < n1 -> summ (fun x => x * x^^m) n1 n2 = n2^^m.+1.
  Proof.
  Admitted.                                 (* 途中！ *)
  
End RFACT.

Section OPTION.
(**
# 補足

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
  
  Notation "n ^^ m" := (rising_factorial n m)
                         (at level 30, right associativity).

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
diff_ffactE' に対応する版
*)
  Lemma summ_ffactE'' (m : nat) (n : nat) :
    1 <= m -> m <= n -> summ (fun x => m.+1 * x^_m) 0 n = n^_m.+1.
  Proof.
    move=> Hm.                         (* 0^_1 = 1 を回避するため。 *)
    move=> Hmn.
    rewrite -[RHS](@summ_diff' (fun x => x^_m.+1)) //.
    - congr (summ _ 0 n).
      apply: (@functional_extensionality' _ _ (leq m)) => x Hmx.
      by rewrite diff_ffactE'.
    - move=> x.
      by apply: ffact_monotone.
  Qed.

(**
diff_rfactE' に対応する版
*)
  Lemma summ_rfactE'' (m : nat) (n : nat) :
    1 <= m -> m <= n -> summ (fun x => m.+1 * x.+1^^m) 0 n = n^^m.+1.
  Proof.
    move=> Hm.                         (* 0^^1 = 1 を回避するため。 *)
    move=> Hmn.
    Check (@summ_diff' (fun x => x^^m)).
    rewrite -[RHS](@summ_diff' (fun x => x^^m.+1)) //.
    - congr (summ _ 0 n).
      apply: (@functional_extensionality' _ _ (leq m)) => x Hmx.
      by rewrite diff_rfactE'.
    - move=> x.
      by apply: rfact_monotone.
  Qed.
  
End OPTION.

(* END *)
