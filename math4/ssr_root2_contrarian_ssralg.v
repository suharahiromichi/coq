(**
√2 が無理数

背理法による「有名な証明」に沿っている。

- https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2020_AW/ssrcoq6.pdf
- https://gitlab.com/proofcafe/nu/-/blob/master/nu_ssrcoq6_3_root2.v

以上の証明と似ているが、主補題の証明に帰納法（整礎帰納法）を使わないことで、簡単であるといえる。

Standard Coq の Real を使用せず、MathComp の rcfType を使用した。
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ssrZ zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Root2.
  
  Section Nat.
    (**
## 自然数の補題
     *)
    Lemma evenP n : reflect (exists m, n = 2 * m) (~~ odd n).
    Proof.
      have -> : ~~ odd n = (2 %| n) by lia.
      apply: (iffP eqP) => [md0 | [k ->]]; last by rewrite modnMr.
      exists (n %/ 2).
      lia.
    Qed.
    
    (* これだと done がうまくいかないのは、なぜだろう。 *)
    Lemma evenP' n : reflect (exists m, n = m * 2) (~~ odd n).
    Proof.
      have -> : ~~ odd n = (2 %| n) by lia.
      by apply: dvdnP.
    Qed.
    
    Lemma even_not_coprime p q : ~~ odd p -> ~~ odd q -> ~~ coprime p q.
    Proof.
      move/evenP => [p' ->].
      move/evenP => [q' ->].
      rewrite coprimeMl 2!coprimeMr.
      Check ~~ [&& coprime 2 2 && coprime 2 q', coprime p' 2 & coprime p' q'].
      done.
    Qed.
    
    Lemma two_p2_implies_not_coprime (p q : nat) :
      2 * q ^ 2 = p ^ 2 -> ~~ coprime p q.
    Proof.
      move=> H.
      have Hq_even : ~~ odd p by lia.           (* q が偶数である。 *)
      case: q H => [| q] H.
      (* p = 0 の場合 *)
      - rewrite /coprime gcdn0.
        lia.
      (* p != 0 の場合 *)
      - have Hp_even : ~~ odd q.+1 by lia.      (* p が偶数である。 *)
        by rewrite even_not_coprime.
    Qed.
  End Nat.
  
  Section Real.
    Open Scope ring_scope.
    Import GRing.                        (* natrM *)
    Import Num.Theory.                   (* sqr_sqrtr, eqr_nat など *)
    
    Variable R : rcfType.                   (* sqrt が計算できる型 *)
    
    Search "sqrt".
    Check Num.Theory.sqr_sqrtr : forall (R : rcfType) (a : R), 0 <= a -> Num.sqrt a ^+ 2 = a.
    
    (* R と nat の相互変換 *)
    Check eqr_nat R : forall m n : nat, (m%:R == n%:R) = (m == n).
    Check ler_nat R : forall m n : nat, (m%:R <= n%:R) = (m <= n)%N.
    Check ltr_nat R : forall m n : nat, (m%:R < n%:R) = (m < n)%N.
    
  (**
## x は無理数である。
   *)
    Definition irrational (x : R) : Prop := forall (p q : nat),
        q <> 0 -> coprime p q -> x <> p%:R / q%:R.
    
  (**
## 証明したいもの ``sqrt 2`` は無理数である。
   *)
    Theorem irrational_sqrt_2 : irrational (Num.sqrt 2).
    Proof.
      move=> p q Hq Hco Hrt.
      move/negPn/negP in Hco.
      apply/Hco/two_p2_implies_not_coprime.

      apply/eqP.
      rewrite -(eqr_nat R) natrM.
      apply/eqP.
      
      Check @sqr_sqrtr R 2 : 0 <= 2 -> Num.sqrt 2 ^+ 2 = 2.
      rewrite -(@sqr_sqrtr R 2).
      
      Check Num.sqrt 2 ^+ 2 * (q ^ 2)%:R = (p ^ 2)%:R.
      - rewrite Hrt.
        field.
        rewrite (eqr_nat R q 0).
        lia.
        
      Check 0 <= 2.
      - auto.
      (*
      - move/eqP in Hq.
        rewrite -(eqr_nat R) in Hq.
        apply/negP.
        done.
       *)
    Qed.
    
  End Real.
End Root2.

(* END *)
