(* Fermat の小定理 *)
(* 2014_3_30 *)
(* suahrahiromichi@gmail.com *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import fintype div bigop prime binomial.

(**
 全体の証明は、
 http://ja.wikipedia.org/wiki/フェルマーの小定理
 証明(1) に沿う、つもり。
 *)

(* この補題は、Coqによる定理証明 2013 12, p.14 *)
(* 乱数列の網羅性 著者：坂口和彦さん *)
Lemma expSS a p :
  a.+1 ^ p.+1 =
  (a ^ p.+1).+1 + \sum_(1 <= k < p.+1 | 0 < k < p.+1) 'C(p.+1, k) * a ^ k.
Proof.
  rewrite -add1n Pascal big_ord_recl big_ord_recr /= /bump /= !add1n
                 bin0 binn subn0 subnn !mul1n exp1n add1n -addnS addnC.
  rewrite -big_nat.
  rewrite (big_addn 0 p.+1 1) subn1 /= big_mkord.
  by congr (_ + _); apply eq_bigr => m _; rewrite exp1n add1n addn1 mul1n.
Qed.

(* pが素数なら、二項定理を使って (m + 1) ^ p を展開したときの、
  m^p + C + 1 の 「C」がpで割りきれることを証明する。 *)
Lemma bino_body__p m p :
  prime p ->
  (\sum_(1 <= i < p | 0 < i < p) 'C(p, i) * m ^ i) %% p == 0.
Proof.
  apply big_ind => //.
    by rewrite mod0n.
  move=> m1 m2 H1 H2 Hp.
    by apply dvdn_add; [apply H1, Hp | apply H2, Hp].
  move=> i H0 Hp.
    by apply dvdn_mulr, prime_dvd_bin. 
Qed.

Lemma mod_m_1p__mp_1 m p :
  prime p.+1 -> m.+1 ^ p.+1 = (m ^ p.+1).+1 %[mod p.+1].
Proof.
  move=> Hp.
  apply/eqP.
  rewrite expSS addSn (eqn_modDl 1)
  -{2}(addn0 (m ^ p.+1)) (eqn_modDl (m ^ p.+1)).
  apply/eqP.
  have H := (bino_body__p m p.+1 Hp).
  move/eqP in H.
  by rewrite mod0n.
Qed.

Lemma mod_1n a b p : a = b %[mod p] -> a.+1 = b.+1 %[mod p].
Proof.
  move=> /eqP H.                            (* move/eqP => H *)
  apply/eqP.
  by rewrite -(addn1 a) -(addn1 b) (eqn_modDr 1 a b p).
Qed.

Theorem Fermat a p:
  prime p.+1 -> a ^ p.+1 = a %[mod p.+1].
Proof.
  move=> Hp.
  elim: a => [|a].
  (* a = 0 *)
  by rewrite exp0n.
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
  rewrite -addn3.
  Check (mod_1n (a.+2 ^ p.+1) (a + 2) p.+1).
  rewrite (mod_1n (a.+2 ^ p.+1) (a + 2) p.+1).
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
