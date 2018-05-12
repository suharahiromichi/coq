(** Programs and Proofs Ilya Sergey *)
(* http://ilyasergey.net/pnp/ *)

(**
4.3 Indexed datatype families and rewriting rules

leqP の使い方について。
 *)
From mathcomp Require Import all_ssreflect.
  
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Goal forall m n, m <= n.
Proof.
  move=> m n.
  case: leqP.
  Undo 1.
  Check (leqP m n) : leq_xor_gtn m n (m <= n) (n < m).
  case: (leqP m n).
  (* m <= n のとき、Goal は true *)
  (* n < m のとき、Goal は false *)
Admitted.

Goal forall n m o p, (m <= n) /\ (o > p) -> False.
Proof.
  move=> n m o p.
  case: leqP.
  Undo 1.
  Check (leqP o p) : leq_xor_gtn o p (o <= p) (p < o).
  case: (leqP o p).
  (* o <= p のとき、Goal は m <= n /\ false -> False *)
  (* p < o のとき、Goal は m <= n /\ true -> False *)
  Admitted.

Lemma huh' n m : (m <= n) /\ (m > n) -> False.
Proof.
  move/andP.
  case: leqP.
  Undo 1.
  Check (leqP m n) : leq_xor_gtn m n (m <= n) (n < m).
  case: (leqP m n).
  
  (* m <= n のとき、Goal は true && false -> False *)
  - done.
  (* n < m のとき、Goal は false && true -> False *)
  - done.
Qed.


Lemma max_is_max m n: n <= maxn m n /\ m <= maxn m n.
Proof.
  rewrite /maxn.
  case: leqP => //.
  move=> H; split.
  - by apply: leqnn.
  - by rewrite ltn_neqAle in H; case/andP: H.

  Restart.
  (* n <= maxn m n /\ m <= maxn m n *)
  rewrite /maxn.
  (* n <= (if m < n then n else m) /\ m <= (if m < n then n else m) *)
  
(*
  move: leqP => H'.
  Check H' n m : leq_xor_gtn n m (n <= m) (m < n).
  case: (H' n m).         (* この n と m の選ばれかたは不明である。 *)
 *)
  Check (leqP n m) : leq_xor_gtn n m (n <= m) (m < n).
  case: (leqP n m).
  
  (* n <= m のとき。 (maxn m n) = m なので、 *)
  (* n <= m -> n <= m /\ m <= m *)
  - done.
    
  (* m < n のとき。 (maxn m n) = n なので、 *)
  (* m < n -> n <= n /\ m <= n *)
  - move=> H; split.
    (* n <= n *)
    + by apply: leqnn.
    (* m < n -> m <= n *)
    + by rewrite ltn_neqAle in H; case/andP: H.
Qed.

Check ltnP : forall m n : nat, ltn_xor_geq m n (n <= m) (m < n).
Check posnP : forall n : nat, eqn0_xor_gt0 n (n == 0) (0 < n).

(* ssrnum.v にも類似の補題がある。 *)

(* END *)
