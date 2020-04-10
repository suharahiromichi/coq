From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Lemma test100 x : (3 %| x) = (3 %| 100 * x).
Proof.
  have -> : 100 = 99 + 1 by [].
  rewrite mulnDl mul1n.
  rewrite dvdn_addr => //=.
    by rewrite dvdn_mulr.
Qed.

Lemma test10 x : (3 %| x) = (3 %| 10 * x).
Proof.
  have -> : 10 = 9 + 1 by [].
  rewrite mulnDl mul1n.
  rewrite dvdn_addr => //=.
    by rewrite dvdn_mulr.
Qed.


Goal forall x y z, 3 %| x -> 3 %| y -> 3 %| z ->
                   (3 %| (100 * x + 10 * y + z)).
Proof.
  move=> x y z Hx Hy Hz.
  rewrite dvdn_addl.
  - rewrite dvdn_addl.
    + by rewrite -test100.
    + by rewrite -test10.
  - done.
Qed.  

Goal forall x y z, (3 %| (x + y + z)) = (3 %| (100 * x + 10 * y + z)).
Proof.
Admitted.


Lemma testXY x y : 3 %| x -> 3 %| y -> 3 %| (x + y).
Proof.
  move=> Hx Hy.
    by rewrite dvdn_addl.
Qed.

Goal forall a b x y, 3 %| (a + b) = (3 %| (x + y)).
Proof.
  move=> a b x y.
  apply/idP/idP => H.
  - apply: testXY.
  



(* ******************************** *)


Lemma test2 n : 0 < 10^n.
Proof.
  elim: n => // n IHn.
  rewrite expnS.
  rewrite -{1}(muln0 10).
    by rewrite ltn_pmul2l.
Qed.

Lemma div3_99 n : 3 %| (10^n - 1).
Proof.
  elim: n => //.
  move=> n IHn.
  rewrite expnS.
  have {1}-> : 10 = 9 + 1 by [].
  rewrite mulnDl.
  rewrite mul1n.
  rewrite -addnBA.
  - rewrite dvdn_addr.
    + done.
    + Search _ (_ %| _ * _).
        by rewrite dvdn_mulr.
  - apply: test2.
Qed.

Lemma test n : 10 ^ n = 10 ^ n - 1 + 1.
Proof.
  rewrite addn1 subn1 prednK //.
  by apply: test2.
Qed.

Goal forall x n, (3 %| x) = (3 %| 10^n * x).
Proof.
  move=> x n.
  have -> : 10^n = (10^n - 1) + 1 by apply: test.
    by rewrite mulnDl mul1n dvdn_addr // dvdn_mulr // div3_99.
Qed.

Goal forall x, (3 %| x) = (3 %| 10 * x).
Proof.
  move=> x.
  have -> : 10 = 9 + 1 by [].
  rewrite mulnDl mul1n.
  rewrite dvdn_addr => //=.
    by rewrite dvdn_mulr.
Qed.

