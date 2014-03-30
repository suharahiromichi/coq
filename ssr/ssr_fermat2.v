(* Fermat の小定理 *)
(* 2014_3_30 *)
(* suahrahiromichi@gmail.com *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import fintype div prime binomial.

(* http://ja.wikipedia.org/wiki/フェルマーの小定理
   の証明(1) に沿う。 *)

Lemma mod_m_1p__mp_1 m p :
  prime p -> (m .+1) ^ p = (m ^ p) .+1 %[mod p].
Proof.
(* =の左辺を二項定理で展開すればよい。 *)
  admit.
Qed.

Lemma mod_1n a b p : a = b %[mod p] -> a.+1 = b.+1 %[mod p].
Proof.
  move=> /eqP H.                            (* move/eqP => H *)
  apply/eqP.
  by rewrite -(addn1 a) -(addn1 b) (eqn_modDr 1 a b p).
Qed.

Theorem Fermat a p:
  p > 0 -> prime p -> a ^ p = a %[mod p].
Proof.
  move=> H Hp.
  elim: a => [|a].
  (* a = 0 *)
  by rewrite exp0n.                         (* p > 0 *)
  elim: a => [|a] H0.
  (* a = 1 *)
  by rewrite exp1n.
  move=> H1 {H0} {H1}.
  elim: a => [|a].
  (* a = 2 *)
  rewrite (mod_m_1p__mp_1 1 p); last done.  (* last は prime p *)
    by rewrite exp1n.
  (* a = k + 1 *)
  move=> H2.
  rewrite (mod_m_1p__mp_1 a.+2); last done. (* last は prime p *)
  rewrite -addn3 (mod_1n (a.+2 ^ p) (a + 2) p).
    by rewrite addn2 addn3.
      by rewrite addn2.
Qed.

(* 使わなかった補題 *)
Lemma mod_2_3n a b p : a = b.+2 %[mod p] -> a.+1 = b.+3 %[mod p].
Proof.
  move=> H.
  apply/eqP.
  move/eqP in H.
  Check eqn_modDr 1 a b.+2 p.
  rewrite -(eqn_modDr 1 a b.+2 p) in H.
  rewrite -addn2 in H.
  rewrite -(addnA b 2 1) in H.
  rewrite addn3 in H.
  rewrite addn1 in H.
  done.
Qed.

Lemma modn_trans l m n d :
  l = m %[mod d] -> m = n %[mod d] -> l = n %[mod d].
Proof.
  move=> Hlm Hmn.
  by rewrite Hlm.
Qed.

(* END *)
