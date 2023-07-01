(**
n 乗の和の因数分解公式
factorization formula for the sum of powers n
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma l_odd_doublenS  k : odd k -> k = k./2.*2.+1.
Proof.
  move=> kO.
  by rewrite odd_halfK // (@ltn_predK 0) // odd_gt0.
Qed.

Lemma a1_exp a k : 0 < a ->
                   a ^ k.+2 - a ^ k = a.+1 * (a ^ k.+1 - a ^ k).
Proof.
  move=> Ha.
  rewrite -[in RHS]addn1.
  rewrite mulnDl 2!mulnBr.
  rewrite -2!expnS 2!mul1n.
  rewrite addnBA; last rewrite leq_pexp2l //=.
  rewrite subnK; last rewrite leq_pexp2l //=.
  done.
Qed.

Lemma ltnSSn n : n < n.+2.
Proof.
  by apply: (ltn_trans (_ : n < n.+1)); first rewrite ltnSn //.
Qed.

Lemma ltnSSSn n : n < n.+3.
Proof.
  apply: (ltn_trans (_ : n < n.+1)); first rewrite ltnSn //.
  by apply: ltnSSn.
Qed.

Check subn_exp : forall m n k : nat, m ^ k - n ^ k = (m - n) * (\sum_(i < k) m ^ (k.-1 - i) * n ^ i).

Lemma sum_last m n a :
  m <= n ->
  \sum_(m <= i < n.+1)(a i) = \sum_(m <= i < n)(a i) + a n.
Proof.
  move=> Hmn.
  by rewrite big_nat_recr.
Qed.

Lemma addn1_exp a k : 0 < a ->
                      (a ^ k.*2.+1).+1 = a.+1 * (\sum_(0 <= i < k.+1) (a ^ i.*2 - a ^ i.*2.-1)).+1.
Proof.
  elim: k => [| k IHk] Ha.
  - rewrite double0 expn1 big_nat1 double0 expn0.
    have -> : (1 - 1).+1 = 1 by done.
    by rewrite muln1.
  - rewrite sum_last //.   (* rewrite big_nat_recr //. でもよいが。 *)
    rewrite -addSn mulnDr -IHk //.
    rewrite addSn.
    congr _.+1.
    (* a ^ k.+1.*2.+1 = a ^ k.*2.+1 + (a + 1) * (a ^ k.+1.*2 - a ^ k.+1.*2.-1) *)
    rewrite [in a ^ k.+1.*2]doubleS [in a ^ k.+1.*2.-1]doubleS.
    rewrite -a1_exp //.
    rewrite [k.*2.+2.-1]/= doubleS.
    rewrite subnKC //.
    rewrite leq_pexp2l //.
    by rewrite ltnSSSn.
Qed.

Lemma dvd_exp_odd a k : 
  0 < a -> odd k -> a.+1 %| (a ^ k).+1.
Proof.
  move=> aP kO.
  (* *** *)
  move: (@l_odd_doublenS k) => -> //.
  rewrite addn1_exp //.
  by apply: dvdn_mulr.
Qed.

(* END *)
