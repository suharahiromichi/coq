(** An Ssreflect Tutorial *)

(** http://hal.archives-ouvertes.fr/docs/00/40/77/78/PDF/RT-367.pdf  *)

Require Import ssreflect ssrbool eqtype ssrnat ssrfun.

(** 3 Arithmetic for Euclidean division *)
(** ユーグリッド互除法 *)

(* 3.2 Deﬁnitions *)

Fixpoint edivn_rec (d m q : nat) : nat*nat :=
  if m - d is m'.+1 then edivn_rec d m' q.+1 else (q, m).
Eval compute in edivn_rec 3 7 1.            (* (2,3) *)

Definition edivn_rec'' d :=
  fix loop (m q : nat) {struct m} :=
  if m - d is m'.+1 then loop m' q.+1 else (q, m).
Eval compute in edivn_rec'' 3 7 1.            (* (2,3) *)

Definition edivn m d :=                     (* 商と余 *)
  if d > 0 then edivn_rec d.-1 m 0 else (0, m).
Eval compute in edivn 7 3.

Definition edivn_rec2 d := fix loop (m q : nat) {struct m} := (* 不使用 *)
  if m - (d - 1) is m'.+1 then loop m' q.+1 else (q, m).
Eval compute in edivn_rec2 4 7 1.            (* (2,3) *)

Definition edivn2 m d :=                    (* 不使用 *)
  if d > 0 then edivn_rec2 d m 0 else (0, m).

CoInductive edivn_spec (m d : nat) : nat * nat -> Type :=
  EdivnSpec q r of (m = q * d + r) & ((d > 0) ==> (r < d)) :
    edivn_spec m d (q, r).
Eval compute in (EdivnSpec 7 3 2 1).       (* 7 / 3 = 2 ... 1 *)
(* :  7 = 2 * 3 + 1 -> (0 < 3) ==> (1 < 3) -> edivn_spec 7 3 (2, 1) *)

(* 3.3 Results *)

Lemma edivnP : forall m d, edivn_spec m d (edivn m d).
Proof.
  rewrite /edivn => m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
  elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
  rewrite subn_if_gt; case: ltnP => [// | le_dm].
  rewrite -{1}(subnK le_dm) -addnS addnA.
  rewrite addnAC -mulSnr.                   (* addnAC を追加した。  *)
  apply (IHn (m - d) q.+1).                 (* apply: IHn でもよい。 *)
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


(* 3.4 Parametric type families and alternative speciﬁcations *)
(* edivn_spec とだいたい同じ *)
CoInductive edivn_spec_right : nat -> nat -> nat * nat -> Type :=
  EdivnSpec_right m d q r of m = q * d + r & (d > 0) ==> (r < d) :
    edivn_spec_right m d (q, r).
Eval compute in (EdivnSpec_right 7 3 2 1).  (* 7 / 3 = 2 ... 1 *)
(* :  7 = 2 * 3 + 1 -> (0 < 3) ==> (1 < 3) -> edivn_right 7 3 (2, 1) *)

CoInductive edivn_spec_left (m d : nat)(qr : nat * nat) : Type :=
  EdivnSpec_left of m = qr.1 * d + qr.2 & (d > 0) ==> (snd qr < d) :
    edivn_spec_left m d qr.
Eval compute in (EdivnSpec_left 7 3 (2,1)).  (* 7 / 3 = 2 ... 1 *)
(* : 7 = (2, 1).1 * 3 + (2, 1).2 ->
       (0 < 3) ==> ((2, 1).2 < 3) -> edivn_spec_left 7 3 (2, 1) *)

Lemma edivnP_right' : forall m d, edivn_spec_right m d (edivn m d).
Proof.
  (* 証明は、edivnP と同じ。 *)
  rewrite /edivn => m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
  elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
  rewrite subn_if_gt; case: ltnP => [// | le_dm].
  rewrite -{1}(subnK le_dm) -addnS addnA.
  rewrite addnAC -mulSnr.                   (* addnAC を追加した。  *)
  apply (IHn (m - d) q.+1).                 (* apply: IHn でもよい。 *)
  apply: leq_trans le_mn; exact: leq_subr.
Qed.

(* ProofCafe yoshihiro503 による。 *)
Lemma edivnP_right : forall m d, edivn_spec_right m d (edivn m d).
Proof.
Check edivnP.
 move=> m d.
 case: (edivnP m d) => q r eq_m_dqr impl_0d_rd.
 by apply: EdivnSpec_right.
Qed.

Lemma edivnP_left' : forall m d, edivn_spec_left m d (edivn m d).
Proof.
  (* 証明は、edivnP と同じ。 *)
  rewrite /edivn => m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
  elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
  rewrite subn_if_gt; case: ltnP => [// | le_dm].
  rewrite -{1}(subnK le_dm) -addnS addnA.
  rewrite addnAC -mulSnr.                   (* addnAC を追加した。  *)
  apply (IHn (m - d) q.+1).                 (* apply: IHn でもよい。 *)
  apply: leq_trans le_mn; exact: leq_subr.
Qed.

(* ProofCafe yoshihiro503 による。 *)
Lemma edivnP_left : forall m d, edivn_spec_left m d (edivn m d).
Proof.
 move=> m d.
 case: (edivnP m d) => q r eq impl.
 by apply EdivnSpec_left.
Qed.

Lemma edivn_eq_right : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
  move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
  set m := q * d + r; have: m = q * d + r by [].
  set d' := d; have: d' = d by [].
  case: (edivnP_right m d') => {m d'} m d' q' r' -> lt_r'd' d'd q'd'r'.
  move: q'd'r' lt_r'd' lt_rd; rewrite d'd d_pos {d'd m} /=.
    wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
  rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addnI->.
    rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
  by rewrite addnS ltnNge mulSn -addnA -Eqr addnCA addnA leq_addr.
Qed.

Lemma edivn_eq_left : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
  move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
  case: (edivnP_left (q * d + r) d) lt_rd; rewrite d_pos /=.
    set q' := (edivn (q * d + r) d).1; set r' := (edivn (q * d + r) d).2.
  rewrite (surjective_pairing (edivn (q * d + r) d)) -/q' -/r'.
    wlog: q r q' r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
  rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addnI->.
    rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
  by rewrite addnS ltnNge mulSn -addnA Eqr addnCA addnA leq_addr.
Qed.
(* .1と.2は直積のfstとsndである。これを使うには、ssrfunが必要である。 *)

(* END *)


(* 証明に直接使われていないもの。 *)

(** 3.1 Basics *)
Variable n : nat.

Lemma three : S (S (S O)) = 3 /\ 2 = 0.+1.+1.
Proof. by [].
Qed.

Lemma concrete_plus : plus 16 64 = 80.
Proof.
    by [].
Qed.

Lemma concrete_le : le 1 3.
Proof.
    by apply: (Le.le_trans _ 2); apply: Le.le_n_Sn.
Qed.

Fixpoint subn_rec (m n : nat) {struct m} :=
  match m, n with
    | m'.+1, n'.+1 => (m' - n')
    | _, _ => m
end.

Lemma concrete_big_leq : 0 <= 51.
Proof.
    by [].
Qed.

Lemma semi_concrete_leq : forall n m, n <= m -> 51 + n <= 51 + m.
Proof.
    by [].
Qed.

Lemma concrete_arith : (50 < 100) && (3 + 4 < 3 * 4 <= 17 - 2).
Proof.
    by [].
Qed.

Lemma plus_commute : forall n1 m1, n1 + m1 = m1 + n1.
Proof.
    by elim=> [| n IHn m]; [elim | change (n.+1 + m) with ((n + m).+1); rewrite IHn; elim: m].
(*  by elim=> [| n IHn m]; [elim | rewrite -[n.+1 + m]/(n + m).+1 IHn; elim: m]. *)
Qed.


CoInductive ltn_xor_geq (m : nat) (n : nat) : bool -> bool -> Set := (* 不使用 *)
| LtnNotGeq : m < n -> ltn_xor_geq m n false true
| GeqNotLtn : n <= m -> ltn_xor_geq m n true false.
Check LtnNotGeq 1 2.                        (* : 1 < 2 -> ltn_xor_geq 1 2 false true *)
Check GeqNotLtn 1 1.                        (* : 0 < 1 -> ltn_xor_geq 1 1 true false *)


(* END *)
