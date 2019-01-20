(* CPU シミュレータ *)
(* インストラクションとしての加算などを定義する。 *)

From mathcomp Require Import all_ssreflect.
Require Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
  
Section Operation.

  Variable N : nat.                         (* word-lenght *)
  Axiom HN : 0 < N.                         (* 0 ではない。 *)
  Hint Resolve HN.
  
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
  
  (* ***** *)
  
  Lemma imodP (i : nat) : i %% N < N.
    by apply ltn_pmod.
  Qed.
  
  Definition negn (i : nat) := if i == 0 then 0 else N - i.
  
  Lemma inegP (i : 'I_N) : negn i < N.
  Proof.
    rewrite /negn.
    case H : ((nat_of_ord i) == 0).
    - done.
    - have H' : N - i < N - 0 -> N - i < N by rewrite (subn0 N).
      apply H'.
      apply ltn_sub2l.
      + done.
      + move/eqP in H.
        apply PeanoNat.Nat.neq_0_lt_0 in H.
          by move/ltP in H.
  Qed.
  
  (* 加算 ADD *)
  Definition iadd (i j : 'I_N) : 'I_N := Ordinal (imodP (i + j)).
  
  (* 2の補数 NEG *)
  Definition ineg (i : 'I_N) : 'I_N := Ordinal (inegP i).
  
  (* 減算 SUB *)
  Definition isub (i j : 'I_N) : 'I_N := Ordinal (imodP (i + ineg j)).
  
  (* ***** *)
  
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
        * done.
      + done.
      + done.
  Qed.
  
  Lemma ijoinP (i j : 'I_N) : njoin i j < N * N.
  Proof.
    by apply (njoinP (ltn_ord i) (ltn_ord j)).
  Qed.

  Definition ijoin (i j : 'I_N) : 'I_(N * N) := Ordinal (ijoinP i j).
  
End Operation.

Extraction iadd.  
(*
let iadd n i j =
  modn (addn (nat_of_ord n i) (nat_of_ord n j)) n
*)

Extraction ineg.
(*
  let ineg n i =
  negn n (nat_of_ord n i)
 *)

Extraction isub.
(* 
let isub n i j =
  modn (addn (nat_of_ord n i) (nat_of_ord n (ineg n j))) n
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


Section Carry.

  Variable N : nat.                         (* word-lenght *)
  Hint Resolve HN.
  
  (*  Lemma iadd2P (i j : 'I_N) : i + j < N.*2. *)
  Lemma iadd2P i j : i < N -> j < N -> i + j < N.*2.
  Proof.
    rewrite -addnn.
    apply ltn_add.
(*
    - by apply ltn_ord.
    - by apply ltn_ord.
*)
  Qed.
  
  Lemma regP (i : 'I_N.*2) : i %% N < N.
  Proof.
      by apply ltn_pmod.
  Qed.

  Lemma carryP (i : 'I_N.*2) : i %/ N < 2.
  Proof.
    rewrite ltn_divLR.
    - by rewrite mul2n.
    - easy.
  Qed.

  Definition iadd2 (i j : 'I_N) : 'I_N.*2 := Ordinal (iadd2P (ltn_ord i) (ltn_ord j)).
  Definition ireg (i : 'I_N.*2) : 'I_N := Ordinal (regP i).
  Definition icarry (i : 'I_N.*2) : 'I_2 := Ordinal (carryP i).

  Definition radd2 (i j : 'I_N) : 'I_N := ireg (iadd2 i j).
  Definition cadd2 (i j : 'I_N) : 'I_2 := icarry (iadd2 i j).

End Carry.

Extraction radd2.
(* 
let radd2 n i j =
  ireg n (iadd2 n i j)
 *)
  
Extraction ireg.
(*
let ireg n i =
  modn (nat_of_ord (double n) i) n

  = modn i n
 *)

(* 第一引数は無視される。 *)
Extraction nat_of_ord.
(* 
let nat_of_ord _ i =
  i
 *)

Extraction iadd2.
(* 
let iadd2 n i j =
  addn (nat_of_ord n i) (nat_of_ord n j)
 *)

Extraction cadd2.
(* 
let cadd2 n i j =
  icarry n (iadd2 n i j)
 *)

Extraction icarry.
(* 
let icarry n i =
  divn (nat_of_ord (double n) i) n
 *)

(* END *)
