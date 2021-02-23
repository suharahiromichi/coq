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
  
  Lemma ffactn2 a : a^_2 = a * a.-1.
  Proof.
    rewrite /falling_factorial /ffact_rec.
      by rewrite muln1.
  Qed.
  
  Lemma ffactn3 a : a^_3 = a * a.-1 * a.-2.
  Proof.
    rewrite /falling_factorial /ffact_rec.
      by rewrite muln1 mulnA.
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
## 和分の公式
 *)
  Lemma summ_nil f a :  summ f a a = 0.
  Proof.
    rewrite /summ.
      by rewrite sum_nil.
  Qed.
  
  Lemma summ_split f g a b :
    a <= b -> summ f a b + summ g a b = summ (fun k => f k + g k) a b.
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
## 下降階乗冪の和分
*)
(**
関数の部分だけを取り出して関数拡張する場合、Standard Coq の
functional_extensionality を使うのではだめで、引数xが m≦x である条件を追加する必要がある。
*)
(*  
  Axiom functional_extensionality_ge_m : 
    forall (m : nat) (f g : nat -> nat),
      (forall x : nat, m <= x -> f x = g x) -> f = g.
*)
(**
### そこそこ一般化した関数拡張の公理
*)
  Axiom functional_extensionality' : 
    forall (A B : Type) (P : A -> Prop) (f g : A -> B),
      (forall (x : A), P x -> f x = g x) -> f = g.
  Check fun (m : nat) => @functional_extensionality' nat nat (leq m).

(**
### 下降階乗冪の和分（0から）

bigopの関数部分をcongrで取り出し、一般化した関数拡張の公理を使用して証明する。
*)
  Lemma summ_ffactE' (m : nat) (b : nat) :
    1 <= m -> m <= b -> summ (fun k => m.+1 * k^_m) 0 b = b^_m.+1.
  Proof.
    move=> Hm.                         (* 0^_1 = 1 を回避するため。 *)
    move=> Hmb.
    rewrite -[RHS](@summ_diff' (fun k => k^_m.+1)) //.
    - congr (summ _ 0 b).
      apply: (@functional_extensionality' _ _ (leq m)) => k Hmk.
        by rewrite diff_ffactE'.
    - move=> x.
        by apply: ffact_monotone.
  Qed.
  
(**
### 下降階乗冪の和分（任意のaから）
*)  
  Lemma summ_ffactE (m : nat) (a b : nat) :
    a <= b -> m < a -> summ (fun k => k * k^_m) a b = b^_m.+1.
  Proof.
  Admitted.                                 (* 途中！ *)

End Summation.

(**
# 応用 (3.5 から平方根の整数部の和)

a = √n (a^2 = n)、ただし a と n は自然数のとき、
a未満の自然数の平方根の整数部の和を求める。
*)
Section SumOfRoot.

(**
## 面倒な計算
*)
  Lemma l_sor_0 a : 2 %/ 3 * (a * (a - 1) * (a - 2)) + 3 %/ 2 * (a * (a - 1)) =
                    1 %/ 6 * (4 * a + 1) * a * (a - 1).
  Proof.
  Admitted.
  
(**
## ``(2/3)*(Σ0,a 3*k^_2δk) + (3/2)*(Σ0,a 2*k^_1δk)`` の計算
 *)
  Lemma l_sor_1 a : 1 < a ->
                    (2 %/ 3) * (summ (fun k => 3 * k^_2) 0 a) +
                    (3 %/ 2) * (summ (fun k => 2 * k^_1) 0 a) =
                    (1 %/ 6) * (4 * a + 1) * a * (a - 1).
  Proof.
    move=> Ha.
    (* summ を消す。 *)
    rewrite summ_ffactE' //.
    rewrite summ_ffactE' //; last by ssromega.
    (* ^_ を消す。 *)
    rewrite ffactn3 ffactn2 -subn2 -subn1.
      by apply: l_sor_0.
  Qed.

(**
## ``Σ0,a (2*k^2 + 3*k^1)δk`` を和分できる項に分解する。
 *)
  Lemma l_sor_2 a : 0 < a ->
                    summ (fun k => (2 %/ 3) * 3 * k^_2 + (3 %/ 2) * 2 * k^_1) 0 a =
                    (2 %/ 3) * (summ (fun k => 3 * k^_2) 0 a) +
                    (3 %/ 2) * (summ (fun k => 2 * k^_1) 0 a).
  Proof.
    move=> Ha.
    rewrite -[LHS]summ_split //.
    rewrite -[in LHS]summ_distr //.
    rewrite -[in LHS]summ_distr //.
    rewrite -[in RHS]summ_distr // mulnA.
    rewrite -[in RHS]summ_distr // mulnA.
    done.
  Qed.

(**
## 総和を和分に変換する。
 *)
  Lemma l_sor_3 a :
    \sum_(0 <= j < a) (2 %/ 3 * 3 * j ^_ 2 + 3 %/ 2 * 2 * j ^_ 1) =
    summ (fun k => (2 %/ 3) * 3 * k^_2 + (3 %/ 2) * 2 * k^_1) 0 a.
  Proof.
      by rewrite /summ.
  Qed.
  
(**
## 2*m*(m - 1) + 3*m を下降階乗冪の式に変換する。
 *)
  Lemma l_sor_4 m :
    2 * m * (m - 1) + 3 * m = (2 %/ 3) * 3 * m^_2 + (3 %/ 2) * 2 * m^_1.
  Proof.
    rewrite /falling_factorial /ffact_rec.
  Admitted.

(**
## m * ((m + 1)^2 - m^2) を計算する。
*)  
  Lemma l_sor_5 m : m * (m.+1^2 - m^2) = 2 * m * (m - 1) + 3 * m.
  Proof.
    rewrite -addn1.
    rewrite mulnBr.
    rewrite sqrnD.
    rewrite !mulnDr.
  Admitted.

(**
## 総和を消す。
 *)
  Lemma l_sor_6 m : \sum_(m^2 <= k < m.+1^2) m = m * (m.+1^2 - m^2).
  Proof.
  Admitted.

(**
## 証明したい定理
 *)
  Lemma sor a : 1 < a ->
                \sum_(0 <= m < a) \sum_(m^2 <= k < m.+1^2) m =
                (1 %/ 6) * (4 * a + 1) * a * (a - 1).
  Proof.
    move=> Ha.
    rewrite (@eq_sum 0 a (fun m => \sum_(m^2 <= k < m.+1^2) m)
                     (fun m => m * (m.+1^2 - m^2)));
      last by move=> m; rewrite l_sor_6.
    rewrite (@eq_sum 0 a (fun m => m * (m.+1^2 - m^2))
                     (fun m => 2 * m * (m - 1) + 3 * m));
      last by move=> m; rewrite l_sor_5.
    rewrite (@eq_sum 0 a (fun m => 2 * m * (m - 1) + 3 * m)
                     (fun m => (2 %/ 3) * 3 * m^_2 + (3 %/ 2) * 2 * m^_1));
      last by move=> m; rewrite l_sor_4.
    rewrite l_sor_3.
    rewrite l_sor_2; last ssromega.
    rewrite l_sor_1; last done.
    done.
  Qed.
  
End SumOfRoot.

(**
################################################
################################################
################################################

# 使わなかった補題
 *)
Section Optional.

(**
関数拡張を使わずに、帰納法でなんとかしようとした場合。うまくいかない。
*)
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

  Lemma l_sor_0' a : 2 %/ 3 * (a * (a - 1) * (a - 2)) + 3 %/ 2 * (a * (a - 1)) =
                    1 %/ 6 * (4 * a + 1) * a * (a - 1).
  Proof.
    (* 右辺を整理する。 *)
    rewrite [in RHS]mulnDr 2![in RHS]mulnDl.
    rewrite {1}[in RHS]mulnBr {1}[in RHS]mulnBr. (* ??? *)
    rewrite addnBA //.
    rewrite addnBAC //.
    rewrite {2}[1 %/ 6 * (4 * a) * a * 1]muln1.
    rewrite -{3}[1 %/ 6 * (4 * a) * a]mulnA.
    rewrite [1 %/ 6 * (4 * a * a)]mulnA.
    rewrite {2}[1 %/ 6 * (4 * a)]mulnA.
    rewrite -{3}[1 %/ 6 * 4 * a * a]mulnA.
    rewrite -{2}[1 %/ 6 * 1 * a * a]mulnA.
    rewrite 3!{1}muln1.
    rewrite [1 %/ 6 * (4 * a)]mulnA.
    have {1}-> : (1 %/ 6 * 4) * a * a * a = (1 %/ 6 * 4) * (a * a * a) by rewrite -!mulnA.
    (*
      1 %/ 6 * 4 * (a * a * a)
      + 1 %/ 6 * (a * a) - 1 %/ 6 * 4 * (a * a)
      - 1 %/ 6 * a
     *)

    (* 左辺を整理する。 *)
    rewrite ![in LHS]mulnBr ![in LHS]mulnBl ![in LHS]mulnBr.
    rewrite [a * 1]muln1.
    have -> : 2 %/ 3 * (a * a * 2) = 2 %/ 3 * 2 * (a * a) by rewrite mulnA.
    have -> : 2 %/ 3 * (a * 2) = 2 %/ 3 * 2 * a by ring.
    rewrite [in LHS]subnBA //.

    rewrite -[in LHS]addnBAC //.
    rewrite -[_ + 2 %/ 3 * 2 * a + _]addnAC.
    rewrite -[_ + (3 %/ 2 * (a * a) - 3 %/ 2 * a) + 2 %/ 3 * 2 * a]addnA.
    have -> : 3 %/ 2 * (a * a) - 3 %/ 2 * a + 2 %/ 3 * 2 * a =
             3 %/ 2 * (a * a) - (3 %/ 2 * a - 2 %/ 3 * 2 * a).
    rewrite [RHS]subnBA //.
    rewrite addnBAC //; last admit.
    Search (_ + (_ - _)).
    rewrite [in LHS]addnBA; try ring.
    (*
      2 %/ 3 * (a * a * a)
      - 2 %/ 3 * (a * a) - 2 %/ 3 * 2 * (a * a) + 3 %/ 2 * (a * a)
      - (3 %/ 2 * a - 2 %/ 3 * 2 * a)
     *)
  Admitted.

End Optional.

(* END *)
