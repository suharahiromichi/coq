Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(* le vs. leq *)

Print le.
Print leq.

Goal forall n, 0 <= n.
done.
Show Proof.
Qed.

Print Le.le_0_n.

Goal forall n m, n.+1 <= m.+1 -> n <= m.
done.
Show Proof.
Qed.

Print le_S_n.
Print le_pred.

Goal forall n, n <= n.
done.
Qed.

Goal forall n, n <= n.+1.
done.
Qed.

Goal forall n, n < n = false.
by elim.
Qed.

(* 加算の可換性 *)

Goal forall n m, m + n = n + m.
elim => // n IH m.
rewrite addnS.
rewrite IH.
by rewrite -addSn.
Qed.

(* about leqP *)

Goal forall n : nat, (n <= 5 \/ 5 < n)%coq_nat.
move=> n.
destruct (Compare_dec.le_gt_dec n 5).
(* NB: does not replace n <= 5 with True *)
auto.
auto.
Show Proof.
Qed.

Goal forall n : nat, (n <= 5) || (5 < n).
move=> n.
case H : (n <= 5).
done.
move/negbT : H.                             (* move/negbT in H . move : H. *)
rewrite -ltnNge.
move=> ->.
done.
(* pros: replace (n <= 5) by true, etc.
   cons: useless rewrite in the 2nd branch, does not scale to three way case analysis *)
Qed.

Goal forall n : nat, (n <= 5) || (5 < n).
move=> n.
case: (leqP n 5).
done.
done.
Qed.




