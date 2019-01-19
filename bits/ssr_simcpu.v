(* CPU シミュレータ *)

From mathcomp Require Import all_ssreflect.
Require Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
  
Section simcpu.

  Variable N : nat.                         (* word-lenght *)
  Axiom HN : 0 < N.                         (* 0 ではない。 *)
  
  Check leq_add : forall m1 m2 n1 n2 : nat, m1 <= n1 -> m2 <= n2 -> m1 + m2 <= n1 + n2.
  
  Lemma ltn_add m1 m2 n1 n2 : m1 < n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
  Proof.
    move=> lt_mn1 lt_mn2.
    rewrite (@ltn_trans (m1 + n2)).
    - done.
    - by rewrite ltn_add2l.
    - by rewrite ltn_add2r.
  Qed.
  
  Lemma leq_ltn_add m1 m2 n1 n2 : m1 <= n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
  Proof.
    move=> le_mn1 lt_mn2.
    rewrite (@leq_trans (m1 + n2)).
    - done.
    - by rewrite ltn_add2l.
    - by rewrite leq_add2r.
  Qed.
  
  (* 加算 ADD *)
  Lemma imodP (i : nat) : i %% N < N.
    apply ltn_pmod.
    by apply HN.
  Qed.
  
  Definition iadd (i j : 'I_N) : 'I_N := Ordinal (imodP (i + j)).
  
  (* 加算 ADD2 notused *)
  Lemma iadd2P (i j : 'I_N) : i + j < N.*2.
  Proof.
    rewrite -addnn.
    apply ltn_add.
    - apply ltn_ord.
    - apply ltn_ord.
  Qed.
  
  Definition iadd2 (i j : 'I_N) : 'I_N.*2 := Ordinal (iadd2P i j).
  
  (* 2の補数 NEG *)
  Definition nneg (i : nat) := if i == 0 then 0 else N - i.
  (*  
  Lemma test : forall n i , n - i < n - 0 -> n - i < n.
  Proof.
    move=> n i H.
    rewrite (subn0 n) in H.
    done.
  Qed.
 *)
  
  Lemma inegP (i : 'I_N) : nneg i < N.
  Proof.
    rewrite /nneg.
    case H : ((nat_of_ord i) == 0).
    - now apply HN.
    - have H' : N - i < N - 0 -> N - i < N by rewrite (subn0 N).
      apply H'.
      apply ltn_sub2l.
      + apply HN.
      + move/eqP in H.
        apply PeanoNat.Nat.neq_0_lt_0 in H.
          by move/ltP in H.
  Qed.
  
  Definition ineg (i : 'I_N) : 'I_N := Ordinal (inegP i).

  (* 語の連結 JOIN *)
  Definition njoin (i j : nat) := i * N + j.
  
  Lemma njoinP (i j : nat) : i < N -> j < N -> njoin i j < N * N.
  Proof.
    move=> Hi Hj.
    rewrite /njoin.
    rewrite -{2}(prednK HN).
    rewrite mulSnr.
    rewrite leq_ltn_add.
    - done.
    - rewrite leq_pmul2r.
      + rewrite -(leq_add2r 1 i N.-1).
        rewrite addn1.
        rewrite [N.-1 + 1]addn1.
        rewrite prednK.
        * done.
        * by apply HN.
      + by apply HN.
      + done.
  Qed.
  
  Lemma ijoinP (i j : 'I_N) : njoin i j < N * N.
  Proof.
    by apply (njoinP (ltn_ord i) (ltn_ord j)).
  Qed.

  Definition ijoin (i j : 'I_N) : 'I_(N * N) := Ordinal (ijoinP i j).
  
End simcpu.

Extraction iadd.  
(*
let iadd n i j =
  modn (addn (nat_of_ord n i) (nat_of_ord n j)) n
*)
Extraction ineg.
(*
  let ineg n i =
  nneg n (nat_of_ord n i)
 *)
Extraction njoin.
(* 
let njoin n i j =
  addn (muln i n) j
 *)
Extraction ijoin.
(* 
let ijoin n i j =
  njoin n (nat_of_ord n i) (nat_of_ord n j)
 *)

(* END *)
