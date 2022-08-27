(**
下降階乗冪 と 上昇階乗冪（Pochhammer 記号）の差分

2022_08_27 @suharahiromichi
*)
From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.
Open Scope nat_scope.

(**
下降階乗冪の差分
 *)

Locate "_ ^_ _".
Print falling_factorial.

Definition diff f := fun x => f x.+1 - f x.
Check fun m n => diff (fun x => x^_m.+1) n = m.+1 * n^_m.
Check fun m n => diff (fun x => x^_m) n = m * n^_m.-1.

Check ffactSS : forall n m : nat, n.+1 ^_ m.+1 = n.+1 * n ^_ m.
Check ffactnSr : forall n m : nat, n ^_ m.+1 = n ^_ m * (n - m).

Lemma diff_ffact' m n : m <= n ->
                        diff (fun x => x^_m.+1) n = m.+1 * n^_m.
                        (* (n.+1)^_(m.+1) - n^_(m.+1) = m.+1 * n^_m. *)

Proof.
  move=> H.
(**
左辺
= (n.+1)^_(m.+1)           - n^_(m.+1)
= n.+1 * n^_m              - n^_m * (n - m)
= n * n^_m  +   n^_m       - n^_m * n  +  n^_m * m
=               n^_m                   +  n^_m * m
=               n^_m  * (1 + m)
= (m.+1)*(n^_m)
= 右辺
*)
  rewrite /diff.
  rewrite ffactSS ffactnSr.
  rewrite mulSn mulnBr.
  rewrite subnBA.
  - rewrite [n ^_ m * n]mulnC.
    rewrite addnAC.
    rewrite -addnBA // subnn addn0.
    rewrite -mulnS mulnC.
    done.
  - by apply: leq_mul.
Qed.

Lemma diff_ffact m n : m <= n ->
                       diff (fun x => x^_m) n = m * n^_m.-1.
  (* (n.+1)^_m - n^_m = m * n^_(m.-1). *)
Proof.
(**
左辺
= (n.+1)^_m                - n^_m
= n.+1 * n^_(m.-1)         - n^_(m.-1) * (n - m + 1)
= n * n^_(m.-1) + n^(m.-1) - n^_(m.-1) * n + n^_(m.-1) * m + n^_(m.-1) * n
=                                            n^_(m.-1) * m
= m * n^_(m.-1)
= 右辺
*)
  case: m => //= m H.
  apply: diff_ffact'.
  by ssromega.
Qed.


(**
上昇階乗冪の差分
 *)
Fixpoint rfact_rec n m := if m is m'.+1 then n * rfact_rec n.+1 m' else 1.
Definition rising_factorial := nosimpl rfact_rec.

Notation "n ^^ m" := (rising_factorial n m)
(at level 30, right associativity).


Section LEMMAS1.
  Lemma rfactn0 n : n ^^ 0 = 1. Proof. by []. Qed.

  Lemma rfact0n m : 0 ^^ m = (m == 0). Proof. by case: m. Qed.

  Lemma rfactnS n m : n ^^ m.+1 = n * n.+1 ^^ m. Proof. by []. Qed.

  Lemma rfactn1 n : n ^^ 1 = n. Proof. exact: muln1. Qed.

  Check ffactSS : forall n m : nat, n.+1 ^_ m.+1 = n.+1 * n ^_ m.
  Check ffactnSr : forall n m : nat, n ^_ m.+1 = n ^_ m * (n - m).

  Lemma rfactSS n m : n.+1 ^^ m.+1 = n.+1 ^^ m * (n + m.+1).
  Proof.
  Admitted.

  Lemma rfactnSr n m : n ^^ m.+1 = n * n.+1 ^^m.
  Proof.
  Admitted.
End LEMMAS1.


Lemma diff_rfact' m n : m <= n ->
                        diff (fun x => x^^m.+1) n = m.+1 * (n.+1)^^m.
Proof.
  rewrite /diff.
  move=> H.
(**
左辺
= (n.+1)^^(m.+1)                            - n^^(m.+1)
= (n.+1)^^m * (n + m.+1)                    - n * (n.+1)^^m
= (n.+1)^^m * n + (n.+1)^^m * m.+1          - n * (n.+1)^^m
=                 (n.+1)^^m * m.+1
= 右辺
*)  
  rewrite rfactSS rfactnSr.
  rewrite mulnDr.
  rewrite addnC.
  rewrite -subnBA.
  - rewrite [n.+1 ^^ m * n]mulnC.
    rewrite subnn subn0.
    rewrite mulnC.
    done.
  - by ssromega.
Qed.

Lemma diff_rfact m n : m <= n ->
                       diff (fun x => x^^m) n = m * (n.+1)^^(m.-1).
Proof.
  case: m => //= m H.
  Check diff_rfact'.
  apply: diff_rfact'.
  by ssromega.
Qed.

(* END *)
