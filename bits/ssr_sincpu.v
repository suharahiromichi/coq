(* CPU シミュレータ *)

From mathcomp Require Import all_ssreflect.
Require Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
  
Section simcpu.

  Lemma idblP {n : nat} (i : 'I_n) : i.*2 < n.*2.
  Proof.
    rewrite -!mul2n ltn_pmul2l.
    - apply ltn_ord.
    - done.
  Qed.
  
  Definition idbl {n : nat} (i : 'I_n) : 'I_n.*2 :=
    Ordinal (idblP i).

  Lemma ltn_add m1 m2 n1 n2 : m1 < n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
  Proof.
    move=> lt_mn1 lt_mn2.
    rewrite (@ltn_trans (m1 + n2)).
    - done.
    - by rewrite ltn_add2l.
    - by rewrite ltn_add2r.
  Qed.
  
  Lemma iaddP {n : nat} (i j : 'I_n) : i + j < n.*2.
  Proof.
    rewrite -addnn.
    apply ltn_add.
    - apply ltn_ord.
    - apply ltn_ord.
  Qed.
  
  Definition iadd {n : nat} (i j : 'I_n) : 'I_n.*2 :=
    Ordinal (iaddP i j).
  
  Lemma imodP {n : nat} (i : nat) : 0 < n -> i %% n < n.
      by apply ltn_pmod.
  Qed.
  
  Definition imod {n : nat} (i : nat) (H : 0 < n) : 'I_n :=
    Ordinal (imodP i H).

  Lemma iadd2P {n : nat} (i j : 'I_n) : 0 < n -> (i + j) %% n < n.
  Proof.
    by apply ltn_pmod.
  Qed.
  
  Definition iadd2 {n : nat} (i j : 'I_n) (H : 0 < n) : 'I_n :=
    Ordinal (iadd2P i j H).

  Lemma iOp2P {n : nat} (i j : 'I_n) op : 0 < n -> (op i j) %% n < n.
  Proof.
    by apply ltn_pmod.
  Qed.
  
  Definition iOp2 {n : nat} (i j : 'I_n) op (H : 0 < n) : 'I_n :=
    Ordinal (iOp2P i j op H).

  Lemma test : forall n i , n - i < n - 0 -> n - i < n.
  Proof.
    move=> n i H.
    rewrite (subn0 n) in H.
    done.
  Qed.
  
  Lemma iNegP' {n : nat} (i : 'I_n) : 0 < n -> 0 < i -> n - i < n - 0.
  Proof.
    move=> Hn Hi.
      by apply ltn_sub2l.
  Qed.
  
  Definition ineg (n i : nat) :=
    if i == 0 then 0 else n - i.
  
  Lemma iNegP {n : nat} (i : 'I_n) : 0 < n -> ineg n i < n.
  Proof.
    move=> Hn.
    rewrite /ineg.
    case H : ((nat_of_ord i) == 0).
    - done.
    - apply test.
      apply ltn_sub2l.
      + done.
      + move/eqP in H.
        Search _ (_ <> 0).
        apply PeanoNat.Nat.neq_0_lt_0 in H.
          by move/ltP in H.
  Qed.
  
  Definition iNeg {n : nat} (i : 'I_n) (H : 0 < n) : 'I_n :=
    Ordinal (iNegP i H).
  
  Lemma leq_ltn_add m1 m2 n1 n2 : m1 <= n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
  Proof.
    move=> le_mn1 lt_mn2.
    rewrite (@leq_trans (m1 + n2)).
    - done.
    - by rewrite ltn_add2l.
    - by rewrite leq_add2r.
  Qed.
  
  Lemma test4 (i j n : nat) : 0 < n -> i < n -> j < n -> i * n + j < n * n.
  Proof.
    move=> Hn Hi Hj.
    Check prednK Hn.
    rewrite -{2}(prednK Hn).
    rewrite mulSnr.
    rewrite leq_ltn_add.
    - done.
    - rewrite leq_pmul2r.
      + rewrite -(leq_add2r 1 i n.-1).
        rewrite addn1.
        rewrite [n.-1 + 1]addn1.
        rewrite prednK.
        * done.
        * done.
      + done.
      + done.
  Qed.

  Lemma test3 (i j m n : nat) : 0 < m -> 0 < n -> i < m -> j < n -> i * n + j < m * n.
  Proof.
    move=> Hm Hn Hi Hj.
  Admitted.
  
End simcpu.

(* たんに double する関数になっている。 *)
Extraction idbl.
(*
let idbl _ _ _ _ n i =
  double (nat_of_ord n i)
*)
Extraction nat_of_ord.
(* 
let nat_of_ord _ i =
  i
 *)
Extraction double.
Extraction iadd.
Extraction imod.
Extraction iadd2.
Extraction iOp2.
Extraction iNeg.

(* END *)
