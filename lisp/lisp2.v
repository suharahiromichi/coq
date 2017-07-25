From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Inductive symbol : Type :=
| SYM_T
| SYM_NIL
| SYM_QUESTION_MARK.

Inductive literal : Type :=
| LIT_NAT (n : nat)
| LIT_SYM (s : symbol).

Inductive star : Type :=
| S_BTM
| S_ATOM (a : literal)
| S_CONS (x y : star).

Definition T := S_ATOM (LIT_SYM SYM_T).
Definition NIL := S_ATOM (LIT_SYM SYM_NIL).
Notation "?" := (S_ATOM (LIT_SYM SYM_QUESTION_MARK)).

Definition CONS (x y : star) := S_CONS x y.
(*
  match (x, y) with
  | (S_BTM, _ ) => S_BTM
  | (_, S_BTM ) => S_BTM
  | (x, y) => S_CONS x y
  end.
*)

Definition CAR  (x : star) :=
  match x with
  | S_BTM => S_BTM
  | S_ATOM _ => S_BTM
  | S_CONS x _ => x
  end.

Definition CDR (x : star) :=
  match x with
  | S_BTM => S_BTM
  | S_ATOM _ => S_BTM
  | S_CONS _ y => y
  end.

Definition ATOM (x : star) :=
  match x with
  | S_BTM => S_BTM
  | S_ATOM _ => T
  | S_CONS _ _ => NIL
  end.

(* EQUAL *)

Definition COND (q a e : star) :=
  match q with
  | S_ATOM (LIT_SYM SYM_NIL) => e
  | _ => a
  end.

(* **** *)

Lemma atom_cons (x y : star) :
  ATOM (CONS x y) = NIL.
Proof.
  done.
Qed.

Lemma car_cons (x y : star) :
  CAR (CONS x y) = x.
Proof.
  done.
Qed.

Lemma cdr_cons (x y : star) :
  CDR (CONS x y) = y.
Proof.
  done.
Qed.

(*
Lemma equal_same (x : star) :
  EQUAL x x.
Proof.
  done.
Qed.

Lemma equal_swap (x y : star) :
  EQUAL x y = EQUAL y x.
Proof.
  rewrite /EQUAL.
  Search "_ = _".
*)

Lemma if_same (x y : star) :
  COND x y y = y.
Proof.
  case: x.
  - done.                                   (* BTM *)
  - case.
    + done.                                 (* NAT *)
    + case.
      * done.                               (* SYM *)
      * done.
      * done.
  - done.                                   (* CONS *)
Qed.

Lemma if_true (x y : star) :
  COND T x y = x.
Proof.
  done.
Qed.

Lemma if_false (x y : star) :
  COND NIL x y = y.
Proof.
  done.
Qed.

Lemma if_nest_E (x y z : star) :
  x = NIL -> COND x y z = z.
Proof.
  move=> H.
  by rewrite H.
Qed.

Lemma if_nest_A (x y z : star) :
  x = T -> COND x y z = y.
Proof.
  move=> H.
  by rewrite H.
Qed.

Lemma cons_car_cdr (x : star) :
  ATOM x = NIL -> (CONS (CAR x) (CDR x)) = x.
Proof.
  intros Hn.
  case Hc: x; rewrite /CONS => /=.
  - by rewrite Hc in Hn.                    (* 前提の矛盾 *)
  - by rewrite Hc in Hn.                    (* 前提の矛盾 *)
  - by [].
Qed.

(* **** *)

Goal forall x,  x = NIL -> COND x T T = T.
Proof.
  intros.
  Check if_nest_E.                          (* 条件付き書き換えの使い方。 *)
  rewrite if_nest_E.
  + done.
  + done.
Qed.

(* END *)

  