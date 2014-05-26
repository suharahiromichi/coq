(** An Ssreflect Tutorial *)

(** http://hal.archives-ouvertes.fr/docs/00/40/77/78/PDF/RT-367.pdf  *)

Require Import ssreflect ssrbool eqtype ssrnat ssrfun.

(** 3 Arithmetic for Euclidean division *)
(** ユーグリッド互除法 *)

(* 3.2 Deﬁnitions *)

Fixpoint edivn_rec (d m q : nat) : nat*nat :=
  if m - d is m'.+1 then edivn_rec d m' q.+1 else (q, m).
Eval compute in edivn_rec 2 7 0.            (* (2,1) *)

Definition edivn m d :=                     (* 商と余 *)
  if d > 0 then edivn_rec d.-1 m 0 else (0, m).
Eval compute in edivn 7 3.                  (* (2,1) *)

(* CoInductive でなくてもよい。 *)
Inductive edivn_spec (m d : nat) : nat * nat -> Type :=
  EdivnSpec q r of m = q * d + r & (d > 0) ==> (r < d) :
    edivn_spec m d (q, r).
Eval compute in (EdivnSpec 7 3 2 1).       (* 7 / 3 = 2 ... 1 *)
(* :  7 = 2 * 3 + 1 -> (0 < 3) ==> (1 < 3) -> edivn_spec 7 3 (2, 1) *)

(* 3.3 Results *)

CoInductive ltn_xor_geq (m : nat) (n : nat) : bool -> bool -> Set :=
| LtnNotGeq : m < n -> ltn_xor_geq m n false true
| GeqNotLtn : n <= m -> ltn_xor_geq m n true false.
Check LtnNotGeq 1 2.                        (* : 1 < 2 -> ltn_xor_geq 1 2 false true *)
Check GeqNotLtn 1 1.                        (* : 0 < 1 -> ltn_xor_geq 1 1 true false *)

Lemma edivnP : forall m d, edivn_spec m d (edivn m d).
Proof.
  rewrite /edivn => m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
  elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=. rewrite ltnS => le_mn.
  rewrite subn_if_gt; case: ltnP => [// | le_dm].
  rewrite -{1}(subnK le_dm) -addnS addnA.
  rewrite addnAC -mulSnr.                   (* addnAC を追加した。  *)
  apply: IHn.
  apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivn_eq : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
  move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
  case: edivnP lt_rd => q' r'; rewrite d_pos /=.
    wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
  rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addnI->.
    rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
    by rewrite addnS ltnNge mulSn -addnA Eqr addnCA addnA leq_addr.
Qed.
Eval compute in edivn 7 3.                  (* (2,1) *)
Eval compute in edivn (2 * 3 + 1) 3.        (* (2,1) *)


(* 略さない書き方 *)
Lemma edivnP' : forall m d, edivn_spec m d (edivn m d).
Proof.
  rewrite /edivn.
  move => m.
  case.
  move=> //=.
  move=> d.
  move=> //=.
  change m with (0 * d.+1 + m) at 1.        (* rewrite -{1}[m]/(0 * d.+1 + m).  *)
  Check (leqnn m).                          (* m <= m *)
  move: (leqnn m).
  move: 0.                                  (* ゴールの中の数字の「0」 *)
  move: {-2}m.
  move: m.

  elim; last move=> n IHn.
  case; last move=> m; move=> q //=.
  case; last move=> m; move=> q //=.

  Check (ltnS m n).                         (* (m < n.+1) = (m <= n) *)
  rewrite (ltnS m n).
  move=> le_mn.                             (* 前提 *)
  Check (@subn_if_gt (nat*nat) m d).
  Check (@subn_if_gt (nat*nat) m d (fun m => edivn_rec d (m - d) q.+1) (q, m.+1)).
  rewrite (@subn_if_gt (nat*nat) m d (fun m => edivn_rec d m q.+1) (q, m.+1)).
  move: ltnP.
  case.
  move=> //.
  move=> le_dm.                             (* 前提 *)
  Check (subnK le_dm).                      (* 引いて足す。 m - d + d = m *)
  rewrite -{1}(subnK le_dm).
  Check (addnS (m - d) d).                  (* m - d + d.+1 = (m - d + d).+1 *)
  rewrite -(addnS (m - d) d).
  Check (addnA (q * d.+1) (m - d) d.+1).    (* q * d.+1 + (m - d + d.+1) = q * d.+1 + (m - d) + d.+1 *)
  rewrite (addnA (q * d.+1) (m - d) d.+1).
  Check (addnAC (q * d.+1) (m - d) d.+1).   (* q * d.+1 + (m - d) + d.+1 = q * d.+1 + d.+1 + (m - d) *)
  rewrite (addnAC (q * d.+1) (m - d) d.+1).
  Check (mulSnr q d.+1).
  rewrite -(mulSnr q d.+1).
  Check (IHn (m - d) q.+1).                 (* m - d <= n -> 
                                 edivn_spec (q.+1 * d.+1 + (m - d)) d.+1 (edivn_rec d (m - d) q.+1) *)
  apply: (IHn (m - d) q.+1).
  move: le_mn.                              (* 前提 *)
  Check (@leq_trans m (m - d) n).           (* m - d <= m -> m <= n -> m - d <= n *)
  move: (@leq_trans m (m - d) n).
  apply.
  Check (leq_subr d m).                     (* m - d <= m *)
  move: (leq_subr d m).
  apply.
Qed.

Lemma edivn_eq' : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
  move=> d q r lt_rd.
  have d_pos: 0 < d.
    move: lt_rd.                            (* 前提 *)
    Check leq_trans.                        (* 1 <= r.+1 -> r.+1 <= d -> 1 <= d *)
    Check (@leq_trans r.+1 1 d).            (* 0 <  r.+1 -> r    <  d -> 0 <  d *)
    move: (@leq_trans r.+1 1 d).
    apply.
    done.
  move: lt_rd.                              (* 前提 *)
  move: edivnP.
  case.
  move=> q' r'.
  rewrite d_pos.                            (* 前提 *)
  rewrite /=.
  wlog: q q' r r' /(q <= q').               (* ├ (P->G)->G *)
  (* (P->G)->G *)
    move: (ltnP q q').
    case.
      eauto.
    symmetry.
    eauto.
  (* ├ P -> G *)
  Check (leq_eqVlt q q').                   (* (q <= q') = (q == q') || (q < q') *)
  rewrite (leq_eqVlt q q').
  Check (@eqP _ q q').                      (* reflect (q = q') (q == q') *)
  move: (@eqP _ q q').                      (* '_' は eqTypeななにか。 *)
  case.
        move=> -> ?.
        Check addnI.
        Check (right_injective).

        Check addn.
        move/addnI.                         (* q' * d + r = q' * d + r' が、 r = r' になる。 *)

        move=> ->.                          (* move -> でもよい。 *)
        by [].
  move=> ? /=.
           
  Check (@leq_pmul2r d q.+1 q' d_pos).      (* (q.+1 * d <= q' * d) = (q < q') *)
  rewrite -((@leq_pmul2r d q.+1 q') d_pos).

  Check (leq_add).                          (* forall m1 m2 n1 n2 : nat, m1 <= n1 -> m2 <= n2 -> m1 + m2 <= n1 + n2 *)
  move/leq_add.                             (* q.+1 * d <= q' * d が、
                          (forall n n0 : nat, n <= n0 -> q.+1 * d + n <= q' * d + n0) になる。 *)
  move=> Hqr Eqr _.

  Check Hqr.                                (* forall n n0 : nat, n <= n0 -> q.+1 * d + n <= q' * d + n0 *)
  move/Hqr.                                 (* r < d が、
                                               q.+1 * d + r.+1 <= q' * d + d  になる。 *)

  move=> {Hqr}.                             (* clear Hqr *)
  Check (addnS (q.+1 * d) r).               (* q.+1 * d + r.+1 = (q.+1 * d + r).+1 *)
  rewrite (addnS (q.+1 * d) r).
  Check (ltnNge (q.+1 * d + r) (q' * d + d)). (* < と ~(>=) の関係 *)
  (* (q.+1 * d + r < q' * d + d) = ~~ (q' * d + d <= q.+1 * d + r) *)
  rewrite (ltnNge (q.+1 * d + r) (q' * d + d)).
  Check (mulSn q d).                        (* q.+1 * d = d + q * d *)
  rewrite (mulSn q d).
  Check (addnA d (q * d) r).                (* d + (q * d + r) = d + q * d + r *)
  rewrite -(addnA d (q * d) r).
  rewrite Eqr.                              (* 前提 *)
  Check (addnCA d (q' * d) r').             (* d + (q' * d + r') = q' * d + (d + r') *)
  rewrite (addnCA d (q' * d) r').
  Check (addnA (q' * d) d r').              (* q' * d + (d + r') = q' * d + d + r' *)
  rewrite (addnA (q' * d) d r').
  Check (leq_addr r' (q' * d + d)).         (* q' * d + d <= q' * d + d + r' *)
  rewrite (leq_addr r' (q' * d + d)).
  by [].
Qed.
Eval compute in edivn 7 3.                  (* (2,1) *)
Eval compute in edivn (2 * 3 + 1) 3.        (* (2,1) *)


(* END *)
