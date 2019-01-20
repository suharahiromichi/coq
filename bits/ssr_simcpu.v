(* CPU シミュレータ *)
(* インストラクションとしての加算などを定義する。 *)

From mathcomp Require Import all_ssreflect.
Require Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Common.

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

End Common.  

Section Instractions.
  
  Variable N : nat.                         (* word-lenght *)
  Axiom HN : 0 < N.                         (* 0 ではない。 *)
  Hint Resolve HN.
  
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
  
  (* ***** *)
  (* ***** *)
  
  Lemma iaddP (i j : nat) : i < N -> j < N -> i + j < N.*2.
  Proof.
    rewrite -addnn.
    by apply ltn_add.
  Qed.
  
  Lemma imodP (i : nat) : i %% N < N.       (* not used *)
    by apply ltn_pmod.
  Qed.
  
  Definition negn (i : nat) := if i == 0 then 0 else N - i.
  Lemma inegnP (i : nat) : negn i < N.
  Proof.
    rewrite /negn.
    case H : (i == 0).
    - done.
    - rewrite {2}(_ : N = N - 0).
      + apply ltn_sub2l.
        * done.
        * move/eqP in H.
          apply PeanoNat.Nat.neq_0_lt_0 in H.
            by move/ltP in H.
      + by rewrite (subn0 N).               (* N = N - 0 *)
  Qed.
  
  Definition neg1 (i : nat) := if i == 0 then 1 else 0.
  Lemma ineg1P (i : nat) : i < 2 -> neg1 i < 2.
  Proof.
    rewrite /neg1 => Hi.
    by case H : (i == 0).
  Qed.

  Lemma icmplP (i : nat) : i < N -> N.-1 - i < N.
  Proof.
    move=> Hi.
    rewrite -subn1.
    rewrite -subnDA.
    rewrite {2}(_ : N = N - 0).
    - apply ltn_sub2l.
      + done.
      + done.
    - by rewrite (subn0 N).                 (* N = N - 0 *)
  Qed.
  
  Lemma ishlP (i : nat) : i < N -> i.*2 < N.*2.
  Proof.
    rewrite -!addnn => Hi.
    by apply ltn_add.
  Qed.
  
  Lemma wordP (i : 'I_N.*2) : i %% N < N.
  Proof.
    by apply ltn_pmod.
  Qed.

  Lemma carryP (i : 'I_N.*2) : i %/ N < 2.
  Proof.
    rewrite ltn_divLR.
    - by rewrite mul2n.
    - easy.
  Qed.
  
  Lemma ishrP (i : nat) : i < N -> i %/ 2 < N.
  Proof.
    move=> Hi.
    rewrite ltn_divLR.
    - rewrite (_ : i = i * 1).
      + by apply ltn_mul.
      + by rewrite muln1.                   (* i = i * 1 *)
    - done.
  Qed.
  
  Lemma parityP (i : nat) : i %% 2 < 2.
  Proof.
    now apply ltn_pmod.
  Qed.
  
  Definition iadd2 (i j : 'I_N) : 'I_N.*2 := Ordinal (iaddP (ltn_ord i) (ltn_ord j)).
  Definition inegn (i : 'I_N) := Ordinal (inegnP i).
  Definition ineg1 (i : 'I_2) := Ordinal (ineg1P (ltn_ord i)).
  Definition icmpl2 (i : 'I_N) := Ordinal (icmplP (ltn_ord i)).
  Definition ishl2 (i : 'I_N) := Ordinal (ishlP (ltn_ord i)).
  
  Definition iword (i : 'I_N.*2) : 'I_N := Ordinal (wordP i).
  Definition icarry (i : 'I_N.*2) : 'I_2 := Ordinal (carryP i).
  (* 加算のcarryは、1:true, 0:false *)
  (* 減算のborrowは、0:true, 1:false *)
  
  Definition ishr2 (i : 'I_N) := Ordinal (ishrP (ltn_ord i)).
  Definition iparity (i : 'I_N) : 'I_2 := Ordinal (parityP i).

  Program Definition izero := @Ordinal 2 0 _.
  Program Definition ione := @Ordinal 2 1 _.
  
  (* 加算 ADD *)
  Definition iadd (i j : 'I_N) : ('I_N * 'I_2) :=
    let: a := iadd2 i j in (iword a, icarry a).
  
  (* 減算 SUB *)
  Definition isub (i j : 'I_N) : ('I_N * 'I_2) :=
    let: a := iadd2 i (inegn j) in (iword a, ineg1 (icarry a)).
  (* 加算のcarryは、1:true, 0:false *)
  (* 減算のborrowは、1:true, 0:false *)
  
  (* 反転 COMPL *)
  Definition icmpl (i : 'I_N) : ('I_N * 'I_2) :=
    (icmpl2 i, ione).
  
  (* 左シフト SHIFT LEFT *)
  Definition ishl (i : 'I_N) : ('I_N * 'I_2) :=
    let: a := ishl2 i in (iword a, icarry a).
  
  (* 右シフト SHIFTR RIGHT *)
  Definition ishr (i : 'I_N) : ('I_N * 'I_2) :=
    (ishr2 i, ineg1 (iparity i)).
  (* 偶数は、carry 1 *)
  (* 奇数は、carry 0 *)
  
End Instractions.

Extraction nat_of_ord. (* let nat_of_ord _ i = i *) (* 第一引数は捨てる。 *)

Extraction negn.
Extraction neg1.
Extraction iadd2.
Extraction inegn.
Extraction ineg1.
Extraction icmpl2.
Extraction ishl2.
Extraction iword.
Extraction icarry.
Extraction izero.                           (* 0 *)
Extraction ione.                            (* S 0 *)

Extraction iadd.
Extraction isub.
Extraction icmpl.
Extraction ishl.
Extraction ishr.

(* END *)
