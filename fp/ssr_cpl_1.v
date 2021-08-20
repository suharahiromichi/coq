From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)
(* Require Import Recdef. *)                (* Function *)
Require Import ssrinv.                      (* inv: *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CPL.
  
  Inductive object :=
  | I
  | dot of object & object
  | prod of (object * object)
  | pair of (object * object)
  | pi1
  | pi2
  | pr of (object * object)
  | O
  | S
  | exp of (object * object)
  | cur of object
  | ev
  .

  Notation "a \; b" := (dot a b).           (* 左結合 *)
  Notation "a \o b" := (dot a b).           (* 右結合 *)
  Check pi1 \; (pi1 \; pi1).
  Check (pi1 \o pi1) \o pi1.
  
  Inductive step : object -> object -> Prop :=
  | id_l   {a}     : step (I \o a) a
  | id_r   {a}     : step (a \o I) a
(*| s_l    {a b c} : step a b -> step (a \o c) (b \o c)
  | s_r    {a b c} : step b c -> step (a \o b) (a \o c) *)
  | dot_al {a b c} : step ((a \o b) \o c) (a \o (b \o c))
  | dot_ar {a b c} : step (a \o (b \o c)) ((a \o b) \o c)
  | prod_c {a b}   : step (prod (a, b))
                          (pair (a \o pi1, b \o pi2))
  | pair_c {a b c} : step (pair (a, b) \o c)
                          (pair (a \o c, b \o c))
  | pair_l {a b}   : step (pi1 \o pair (a, b)) a
  | pair_r {a b}   : step (pi2 \o pair (a, b)) b
  | pr_l   {a b}   : step (     pr (a, b) \o S)
                          (b \o pr (a, b))
  | pr_r   {a b}   : step (     pr (a, b) \o O) a
  | ev_d   {a}     : step (ev \o prod (cur a, I)) a
  | ev_a   {a b c} : step (ev \o pair (cur a \o c, b))
                          (a  \o pair (c, b))
  | exp_e  {a b}   : step (exp (a, b))
                          (cur b \o ev \o prod (I, a))
  .
  
  Axiom AX : forall {a b}, step a b -> a = b.
  
  Lemma ida1 a : a \o I = a.
  Proof.
      by apply: (AX id_r).
  Qed.
  
  Lemma id1a a : I \o a = a.
  Proof.
      by apply: (AX id_l).
  Qed.
  
  Lemma dotA a b c : a \o b \o c = a \o (b \o c). (* 左結合 = 右結合 *)
  Proof.
      by apply: (AX dot_al).
  Qed.
  
  Lemma prodC a b : prod (a, b) = pair (a \o pi1, b \o pi2).
  Proof.
      by apply: (AX prod_c).
  Qed.

  Lemma pairC a b c : pair (a, b) \o c = pair (a \o c, b \o c).
  Proof.
      by apply: (AX pair_c).
  Qed.
  
  Lemma pairL a b : pi1 \o pair (a, b) = a.
  Proof.
      by apply: (AX pair_l).
  Qed.
  
  Lemma pairR a b : pi2 \o pair (a, b) = b.
  Proof.
      by apply: (AX pair_r).
  Qed.
  
  Lemma prL a b : pr (a, b) \o S = b \o pr (a, b).
  Proof.
      by apply: (AX pr_l).
  Qed.
  
  Lemma prR a b : pr (a, b) \o O = a.
  Proof.
      by apply: (AX pr_r).
  Qed.
  
  Lemma eval a b c : ev \o pair (cur a \o b, c) = a \o pair (b, c).
  Proof.
    by apply: (AX ev_a).
  Qed.
  
  (* eval の終了時の特別な形 *)
  Lemma eval1 a b : ev \o pair (cur a, b) = a \o pair (I, b).
  Proof.
    rewrite -[cur a]ida1.
      by apply: eval.
  Qed.
  
(**
sample
*)  
  
  Definition one := S \o O.
  Definition two := S \o S \o O.

  Definition double := pr (O, S \o S).

  Goal double \o one = two.
  Proof.
    rewrite /double /one.
    rewrite -!dotA.                         (* 左結合 *)
    rewrite prL.
    rewrite !dotA.                          (* 右結合 *)
    rewrite prR.
    rewrite /two.
    rewrite !dotA.                          (* 右結合 *)
    done.
  Qed.
  
(**
add
*)
  Definition add := ev \o pair (pr (cur pi2,
                                    cur (S \o ev)) \o pi1,
                                pi2).
  
  Goal add \o pair (one, one) = two.
  Proof.
    rewrite /add /one.
    rewrite !dotA.                          (* 右結合 *)
    rewrite pairC.
    rewrite !dotA.                          (* 右結合 *)
    rewrite pairL.
    rewrite -!dotA.                         (* 左結合 *)
    rewrite prL.
    rewrite !dotA.                          (* 右結合 *)
    rewrite prR.
    rewrite eval.
    rewrite !dotA.                          (* 右結合 *)
    rewrite eval1.
    rewrite !pairR.
    rewrite /two.
    rewrite !dotA.                          (* 右結合 *)
    done.
  Qed.

  Definition add_alt := ev \o prod (pr (cur pi2, cur (S \o ev)), I).
  
  Goal add_alt \o pair (one, one) = two.
  Proof.
    rewrite /add /one.
    rewrite !dotA.                          (* 右結合 *)
    rewrite prodC.
    rewrite pairC.
    rewrite !dotA.                          (* 右結合 *)
    rewrite pairL.
    rewrite -!dotA.                         (* 左結合 *)
    rewrite prL.
    rewrite !dotA.                          (* 右結合 *)
    rewrite prR.
    rewrite eval.
    rewrite !dotA.                          (* 右結合 *)
    rewrite eval1.
    rewrite !pairR.
    rewrite /two.
    rewrite !dotA.                          (* 右結合 *)
    rewrite id1a.
    done.
  Qed.
  
(**
mult
*)  
  Definition mult := ev \o prod (pr (cur (O \o I),
                                     cur (add \o pair (ev, pi2))),
                                 I).

(**
fact
*)
  Definition fact := pi1 \o pr (pair (S \o O, O),
                                pair (mult \o pair (S \o pi2,
                                                    pi1),
                                      S \o pi2)).

End CPL.


id)
mult = ev.prod(pr(curry(zero.!),
curry(add.pair(ev, pi2))), id)
fact = pi1.pr(pair(s.zero, zero),
pair(mult.pair(s.pi2, pi1), s.pi2))

(* END *)
