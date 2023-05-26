(**
上昇階乗冪と多重集合係数
========================

@suharahiromichi

2020/06/30
*)

From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

Coq/MathComp の binomial.v ライブラリで遊んでいます。

ここで定義されているのは、
順列（下降階乗冪、 falling factorial）と、
組合せ（二項係数、binomial coeficient）です。

それらについては大抵の補題が証明されているので、
これらに良く似た（対応した）、上昇階乗冪 (rising factorial) と、
重複組合せ（多重集合係数、multiset coeficent, Homogeneous Product）を定義して、
いくつかの性質を証明してみます。

このファイルは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_msc_qiita.v


また、

https://github.com/suharahiromichi/coq/blob/master/common/ssromega.v


も必要です。

*)
(**
## 定義

- 下降階乗冪（binomial.vで定義）は、nをからそれを含むm個の下降積です。
MathCompでは、「$n^\underline{m}$=``n^_m``」と表記します。

$$ n^\underline{m} = \prod_{k=1}^{m}(n - k + 1) $$

- 二項係数は（binomial.vで定義）、MathCompでは、

```math

{n\choose m}=C(n, m)
```

と表記します。次の漸化式で定義されます。

```math

\begin{eqnarray}
C(n, 0) &=& 1 \\
C(n, m) &=& C(n-1, m-1) C(n-1, m)\\
\end{eqnarray}
```

- 上昇階乗冪（ここで定義）は、nをからそれを含むm個の上昇積です。
「$n^\overline{m}$=``n^^m``」と表記します。

$$ n^\overline{m} = \prod_{k=1}^{m}(n + k - 1) $$


- 多重集合係数（ここで定義）は、

```math

\left(\!\!{n\choose m}\!\!\right) = H(n, m)
```

と表記することにします。二項係数と同様に漸化式で定義されます。

```math

\begin{eqnarray}
H(n, 0) &=& 1 \\
H(n, m) &=& H(n-1, m) H(n, m-1)\\
\end{eqnarray}
```
*)
(**
## 目標

以下では、下降階乗冪と上昇階乗冪の関係：

$$ (n+m)^\underline{m} = (n+1)^\overline{m} $$

および、二項係数と多重集合係数の関係：

$$ C(n + m, m) = H(n + 1, m) $$

を証明することを目標にします。
なお、有理数は導入せず、自然数の割算と剰余を使います。

このとき、``d | n`` は n は d を割り切る（除数 | 被除数）こととし、
四則演算より優先度が低いものとします。

適宜括弧を補って表記します。
*)

(**
# 上昇階乗冪 (rising factorial)

## 定義

単純な再帰関数として定義します。演算子``^^``を定義します。
*)
Section DEFINE1.
  Fixpoint rfact_rec n m := if m is m'.+1 then n * rfact_rec n.+1 m' else 1.
  
  Definition rising_factorial := nosimpl rfact_rec.
End DEFINE1.
  
Notation "n ^^ m" := (rising_factorial n m)
(at level 30, right associativity).

(**
## 上昇階乗冪の補題
*)

Section LEMMAS1.
  
  Lemma rfactn0 n : n ^^ 0 = 1. Proof. by []. Qed.

  Lemma rfact0n m : 0 ^^ m = (m == 0). Proof. by case: m. Qed.
  
  Lemma rfactnS n m : n ^^ m.+1 = n * n.+1 ^^ m. Proof. by []. Qed.
  
  Lemma rfactn1 n : n ^^ 1 = n. Proof. exact: muln1. Qed.

  Lemma rfactSS n m : n * n.+1 ^^ m.+1 = n ^^ m * (n + m) * (n + m + 1).
  Proof.
    elim: m n => [| m IHm] n.
    - rewrite rfactn0 mul1n addn0 addn1.
      rewrite rfactn1.
      done.
    - rewrite rfactnS.
      rewrite (IHm n.+1).
      rewrite ?mulnA.
      congr (_ * _ * _); by ssromega.
  Qed.
  
  Lemma rfactnSr n m : n ^^ m.+1 = n ^^ m * (n + m).
  Proof.
    elim: m n => [| m IHm] n.
    - rewrite rfactn1.
      by rewrite rfactn0 mul1n addn0.
    - rewrite rfactnS.
      rewrite IHm.
      rewrite mulnA.
      rewrite rfactnS.
      by rewrite addSn addnS.
  Qed.
  
  Lemma rfactnn n : 1 ^^ n = n`!.
  Proof.
    elim: n => [| n IHn] //.
    rewrite rfactnSr add1n IHn.
    by rewrite factS mulnC.
  Qed.
  
  Lemma rfact_fact n m : n`! * n.+1 ^^ m = (n + m)`!.
  Proof.
    elim: m n => [| m IHn] n.
    - by rewrite rfactn0 muln1 addn0.
    - rewrite rfactnS.
      have -> : n + m.+1 = n.+1 + m by ssromega.
      rewrite -IHn.
      rewrite !mulnA.
      rewrite factS [n.+1 * n`!]mulnC.
      done.
  Qed.
  
  Lemma rfact_factd n m : n.+1 ^^ m = (n + m)`! %/ n`!.
  Proof.
    rewrite -rfact_fact.
    rewrite mulnC mulnK; first done.
    by rewrite fact_gt0.
  Qed.
End LEMMAS1.

(**
## 定理：下降階乗冪と上昇階乗冪の関係
*)  
Section TH1.
  
  Lemma ffact_rfact n m : (n + m) ^_ m = n.+1 ^^ m.
  Proof.
    elim: m n => [| m IHm] n.
    - by rewrite ffactn0 rfactn0.
    - rewrite rfactnS ffactnS.
      have -> : (n + m.+1).-1 = n + m by ssromega.
      rewrite IHm -rfactnS [LHS]mulnC.
      have -> : n + m.+1 = m.+1 + n by ssromega.
      rewrite rfactnSr !addSn [m + n]addnC.
      done.
  Qed.
End TH1.

(**
# 多重集合係数 (multiset coeficent, Homogeneous Product)

## 定義

漸化式で定義しますが、そのまま再帰関数にしただけでは、停止性が判定できないので、
CoqのFunctionコマンドを使い、再帰呼出の毎に、ふたつの引数の合計が少なくなることを
明示します。そして、要求にしたがって証明をつけ``Defined``で終わります。
*)

Section DEFINE2.

  Local Definition sum (p : nat * nat) : nat :=  (* nat と nat ペアの合計 *)
    match p with
    | (n, m) => n + m
    end.

  Function multiset_rec p {measure sum p} : nat :=
    match p with
    | (n'.+1 as n, m'.+1 as m)  => multiset_rec (n', m) + multiset_rec (n, m')
    | (_, 0) => 1
    | (0, _.+1) => 0 
    end.
  Proof.
    - move=> p n m n' _ m' _ _.
      rewrite /sum.
      apply/ltP.
      by rewrite [n'.+1 + m'.+1]addnS.
    - move=> p n m n' _ m' _ _.
      rewrite /sum.
      apply/ltP.
      by rewrite [n'.+1 + m'.+1]addSn.
  Defined.
  
  Definition multiset := nosimpl multiset_rec.
End DEFINE2.

(**
演算子``H(_,_)``を定義します。
*)
Notation "''H' ( n , m )" := (multiset (n, m))
(at level 8, format "''H' ( n ,  m )") : nat_scope.
  
(**
Functionコマンドで定義した場合、関数定義の展開は通常のunfoldタクティクではなく、
multiset_rec_equation による書き換えによって行いす。
*)  
  Check multiset_rec_equation.

(**
## 多重集合の補題
*)

Section LEMMAS2.
  
  Lemma msc0 (n : nat) : 'H(n, 0) = 1.
  Proof. by case: n. Qed.

  Lemma msc0n (m : nat) : 'H(0, m) = (m == 0).
  Proof. by case: m. Qed.
  
  Lemma mscS n m : 'H(n.+1, m.+1) = 'H(n, m.+1) + 'H(n.+1, m).
  Proof.
      by rewrite /multiset multiset_rec_equation.
  Qed.
  
  Lemma msc1 n : 'H(n, 1) = n.
  Proof.
    elim: n => //=.
    move=> n IHn.
    by rewrite mscS msc0 IHn addn1.
  Qed.

  Lemma msc1n (n : nat) : 'H(1, n) = 1.
  Proof.
    elim: n => //=.
    move=> n IHn.
    rewrite mscS msc0n add0n.
    done.
  Qed.
  
  Lemma mul_msc_diag n m : n * 'H(n.+1, m) = m.+1 * 'H(n, m.+1).
  Proof.
    elim: n m => [| n IHn] m.
    - by rewrite mul0n msc0n /= muln0.
    - elim: m n IHn => [| m IHm] n IHn.
      + by rewrite msc0 muln1 msc1 mul1n.
      + rewrite mscS mulnDr IHm.
        * rewrite ['H(n.+1, m.+2)]mscS mulnDr -IHn.
          rewrite -!mulnDl.
          congr (_ * _).
          by ssromega.
        * done.
  Qed.
  
  Lemma msc_fact n m : 'H(n.+1, m) * n`! * m`! = (n + m)`!.
  Proof.
    elim: m n => [| m IHm] n.
    - rewrite msc0 mul1n.
      rewrite fact0 muln1.
      rewrite addn0.
      done.
    - rewrite [(m.+1)`!]factS.
      rewrite !mulnA.
      rewrite [_ * m.+1]mulnC.
      rewrite !mulnA.
      rewrite -mul_msc_diag.
      
      rewrite [_ * n`!]mulnC mulnA.
      rewrite [n`! * n.+1]mulnC -factS.
      rewrite [(n.+1)`! * 'H(n.+2, m)]mulnC.
      rewrite IHm.
      
      rewrite addSnnS addnS.
      done.
  Qed.
  
  Lemma msc_factd (n m : nat) : 'H(n.+1, m) = (n + m)`! %/ (n`! * m`!).
  Proof.
    rewrite -msc_fact.
    rewrite -mulnA.
     rewrite mulnK.
    + done.
    + rewrite muln_gt0.
      rewrite 2!fact_gt0.
      done.
  Qed.

(**
ここで、``(n! m!) | (n + m)!`` を証明しておきます。

``H(n, m) n! m! = (n + m)!`` から自明ですが、
``C(n, m) m! (n - m)! = n!`` からも証明することができます。

https://qiita.com/suharahiromichi/items/9e0eb6d8e762cf31d047
*)  
  Lemma divn_fact_mul_add_fact (n m : nat) : n`! * m`! %| (n + m)`!.
  Proof.
    rewrite -msc_fact.
    rewrite -[n`! * m`!]mul1n.
    rewrite -['H(n.+1, m) * n`! * m`!]mulnA.
      by apply: dvdn_mul.
  Qed.

(**
多重集合係数と下降階乗冪の関係です。
*)  
  Lemma msc_ffact (n m : nat) : 'H(n.+1, m) * m`! = (n + m) ^_ m.
  Proof.
    case: n => [| n].
    - rewrite msc1n mul1n.
      rewrite add0n ffactnn.
      done.
    - rewrite ffact_factd.
      + rewrite msc_factd.
        rewrite divn_mulAC.
        * rewrite divnMr.
          ** rewrite -addnBA; last done.
               by rewrite subnn addn0.    (* subnn n : n - n = 0 *)
          ** by rewrite fact_gt0.
        * by rewrite divn_fact_mul_add_fact.
      + by ssromega.
  Qed.
  
  Lemma msc_ffactd n m : 'H(n.+1, m) = (n + m) ^_ m %/ m`!.
  Proof.
      by rewrite -msc_ffact mulnK ?fact_gt0.
  Qed.

(**
多重集合係数と上昇階乗冪の関係です。
 *)
  Lemma msc_rfact (n m : nat) : 'H(n, m) * m`! = n ^^ m.
  Proof.
    elim: m n => [| m IHm] n.
    - by rewrite msc0 mul1n.
    - rewrite factS mulnA ['H(n, m.+1) * m.+1]mulnC.
      rewrite -mul_msc_diag -mulnA.
        by rewrite IHm.
  Qed.
  
  Lemma msc_rfactd n m : 'H(n, m) = (n ^^ m) %/ m`!.
  Proof.
      by rewrite -msc_rfact mulnK ?fact_gt0.
  Qed.
End LEMMAS2.

(**
# 定理：二項係数と多重集合の関係

二項係数と下降階乗冪、多重集合と下降階乗冪の関係を使って証明できます。
*)
Section TH2.  
  
  Lemma multiset_binomial (n m : nat) : 'H(n.+1, m) = 'C(n + m, m).
  Proof.
    rewrite bin_ffactd.
    rewrite msc_ffactd.
    done.
  Qed.
  
End TH2.

(* END *)
