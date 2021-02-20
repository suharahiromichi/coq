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
# 下降階乗冪 の差分
*)

Section Difference.

  Definition Diff f := fun x => f x.+1 - f x.

(**
## 証明しやすいかたち：

```Δx^_(m + 1) / Δx = (m + 1) * x^_m```
*)  
  Lemma diff_ffactE' (m : nat) (x : nat) :
    m <= x -> Diff (fun x => x^_m.+1) x = m.+1 * x^_m.
  Proof.
    move=> Hmx.
    rewrite /Diff.
    rewrite ffactSS ffactnSr [x^_m * (x - m)]mulnC.
    rewrite mulnBl mulSnr.
    rewrite subnBA; last first.
    - by rewrite leq_mul.
    - rewrite -[x * x^_m + x^_m + m * x^_m]addnA.
      rewrite -{2}[x * x^_m]addn0 subnDl subn0.
      rewrite -mulSn.
      done.
  Qed.
  
(**
## より直感的かかたち：

```Δx^_m / Δx = m * x^_(m - 1)```
*)  
  Lemma diff_ffactE (m : nat) (x : nat) :
    0 < m ->  m < x -> Diff (fun x => x^_m) x = m * x^_m.-1.
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
  Proof.
      by rewrite /= muln1.
  Qed.

(**
## 特殊なかたち；

```Δx/Δx = 1```
*)  
  Check @diff_ffactE' 0
    : forall x : nat, 0 <= x -> Diff (fun x => x^_1) x = 1 * x^_0.

  Lemma diff_idE (x : nat) : Diff id x = 1.
  Proof.
    rewrite -[RHS](ffact0 x) -[RHS]mul1n.
    rewrite -(@diff_ffactE' 0 x); last first.
    - done.
    - rewrite /falling_factorial /ffact_rec.
      rewrite /Diff.
        by ssromega.
  Qed.
  
End Difference.

(* END *)
