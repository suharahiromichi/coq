(**
√2 が無理数

背理法による「有名な証明」に沿っている。

- https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2020_AW/ssrcoq6.pdf
- https://gitlab.com/proofcafe/nu/-/blob/master/nu_ssrcoq6_3_root2.v

以上の証明と似ているが、主補題の証明に帰納法（整礎帰納法）を使わないことで、簡単であるといえる。
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ssrZ zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Root2.

  (**
## 補題
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

  Section Real.
    Require Import Reals Field.     (* 実数とそのためのfield タクティク *)
    (* 前に出すと、lia がうまくいかない。 *)
    (*
      Module Import GRing.
     *)

  (**
## 無理数である。
   *)
    Definition irrational (x : R) : Prop := forall (p q : nat),
        q <> 0 -> coprime p q -> x <> (INR p / INR q)%R.
    
  (**
## 証明したいもの ``sqrt 2`` は無理数である。
   *)
    Theorem irrational_sqrt_2 : irrational (sqrt (INR 2)).
    Proof.
      move=> p q Hq Hco Hrt.
      move/negPn/negP in Hco.
      apply/Hco/two_p2_implies_not_coprime/INR_eq.
      move/not_INR in Hq.
      
      Check INR (p * p) = INR (q * q).*2.
      
      rewrite !mult_INR -(sqrt_def (INR 2)).
      - rewrite ?Hrt.
        Check (INR p * INR p)%R = (INR p / INR q * (INR p / INR q) * (INR q * INR q))%R.
        by field.
      - by auto with real.
    Qed.

  End Real.
End Root2.

(* END *)
