From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
Symbol
 *)

Inductive symbol : Type :=
| SYM_T
| SYM_NIL
| SYM_QUESTION_MARK.

Definition eqSym (s t : symbol) : bool :=
  match (s, t) with
  | (SYM_T, SYM_T) => true
  | (SYM_NIL, SYM_NIL) => true
  | (SYM_QUESTION_MARK, SYM_QUESTION_MARK) => true
  | _ => false
  end.

Lemma symbol_eqP : forall (x y : symbol), reflect (x = y) (eqSym x y).
Proof.
  move=> x y.
    by apply (iffP idP); case x; case y.
Qed.
Definition symbol_eqMixin := @EqMixin symbol eqSym symbol_eqP.
Canonical symbol_eqType := @EqType symbol symbol_eqMixin.

(**
Literal
 *)

Inductive literal : Type :=
| LIT_NAT (n : nat)
| LIT_SYM (s : symbol).

Definition eqLit (a b : literal) : bool :=
  match (a, b) with
  | (LIT_NAT n, LIT_NAT m) => n == m
  | (LIT_SYM s, LIT_SYM t) => s == t        (* eqSym *)
  | _ => false
  end.

Lemma literal_eqP : forall (x y : literal), reflect (x = y) (eqLit x y).
Proof.
  move=> x y.
  apply (iffP idP).
  - admit.
  - move=> H; rewrite H.
    case: y H => n H1.
    by rewrite /eqLit.
    by rewrite /eqLit.
Admitted.
Definition literal_eqMixin := @EqMixin literal eqLit literal_eqP.
Canonical literal_eqType := @EqType literal literal_eqMixin.

(**
Star (S-EXP)
*)

Inductive star : Type :=
| S_ATOM (a : literal)
| S_CONS (x y : star).

Fixpoint eqStar (x y : star) : bool :=
  match (x, y) with
  | (S_ATOM a, S_ATOM b) => a == b          (* eqLit *)
  | (S_CONS x1 y1, S_CONS x2 y2) =>
    eqStar x1 x2 && eqStar y1 y2
  | _ => false
  end.

Lemma star_eqP : forall (x y : star), reflect (x = y) (eqStar x y).
Proof.
  move=> x y.
  apply (iffP idP).
  - admit.
  - move=> H; rewrite H.
    case: y H => l.
    + by move=> y; rewrite /eqStar.
    + move=> y H. simpl.
Admitted.
Definition star_eqMixin := @EqMixin star eqStar star_eqP.
Canonical star_eqType := @EqType star star_eqMixin.

Notation "'T" := (S_ATOM (LIT_SYM SYM_T)).
Notation "'NIL" := (S_ATOM (LIT_SYM SYM_NIL)).
Notation "'?" := (S_ATOM (LIT_SYM SYM_QUESTION_MARK)).

Definition CONS (x y : star) := S_CONS x y.

Definition CAR  (x : star) : star :=
  match x with
  | S_ATOM _ => 'NIL
  | S_CONS x _ => x
  end.

Definition CDR (x : star) : star :=
  match x with
  | S_ATOM _ => 'NIL
  | S_CONS _ y => y
  end.

Definition ATOM (x : star) : star :=
  match x with
  | S_ATOM _ => 'T
  | S_CONS _ _ => 'NIL
  end.

Definition COND (q a e : star) : star :=
  if (eqStar q 'NIL) then e else a.

Definition EQUAL (x y : star) : star :=
  if (eqStar x y) then 'T else 'NIL.

(* **** *)

(* 否定が扱えるように、一旦boolを経由する。 *)
Coercion is_not_nil (x : star) : bool := ~~ eqStar x 'NIL.

Check (ATOM 'T) : star.
Check (ATOM 'T) : Prop.
Check ~ (ATOM 'T) : Prop.

Check (ATOM (CONS 'T 'T)) : star.
Check (ATOM (CONS 'T 'T)) : Prop.
Check ~ (ATOM (CONS 'T 'T)) : Prop.

(* **** *)

Lemma atom_cons (x y : star) :
  ATOM (CONS x y) = 'NIL.
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

Lemma equal_same (x : star) :
  EQUAL x x.
Proof.
  elim: x => a.
  - rewrite /EQUAL //=.
    case: a.
    + move=> n; rewrite /eqLit //=.
      case Hc : (n == n).
(*
      * done.
      * admit.
    + move=> s; rewrite /eqLit //=.
      case Hc : (eqSym s s).
      * done.
      * admit.
    + move=> H1 y H2.
      rewrite /EQUAL /=.
      case Hc : (eqStar a a && eqStar y y).
      * done.
      * admit.
*)
Admitted.

Lemma equal_swap (x y : star) :
  EQUAL x y = EQUAL y x.
Proof.
  rewrite /EQUAL.
  admit.
Admitted.

Lemma if_same (x y : star) :
  COND x y y = y.
Proof.
  case: x.
  - case.
    + done.                                 (* NAT *)
    + case.
      * done.                               (* SYM *)
      * done.
      * done.
  - done.                                   (* CONS *)
Qed.

Lemma if_true (x y : star) :
  COND 'T x y = x.
Proof.
  done.
Qed.

Lemma if_false (x y : star) :
  COND 'NIL x y = y.
Proof.
  done.
Qed.

Lemma if_nest_E (x y z : star) :
  x = 'NIL -> COND x y z = z.
Proof.
  move=> H.
  by rewrite H.
Qed.

Check @if_nest_E (ATOM 'T) 'NIL 'T : ATOM 'T = 'NIL -> COND (ATOM 'T) 'NIL 'T = 'T.

Goal (COND (ATOM 'T) 'T
           (COND (ATOM 'T) 'NIL 'T)) = 'T.
Proof.
  rewrite {1}/COND.
  case Hc : (eqStar (ATOM 'T) 'NIL).
  - rewrite (@if_nest_E (ATOM 'T) 'NIL 'T).
    + done.
    + simpl in Hc.
      by rewrite /eqLit /eqSym in Hc.
  - done.
Qed.

Lemma star_nil_nil (x : star) :
  x = 'NIL -> eqStar x 'NIL = true.
Proof.
  move=> H.
  by rewrite H /= /eqLit /eqSym.
Qed.

Lemma if_nest_A (x y z : star) :
  x <> 'NIL -> COND x y z = y.
Proof.
  move=> H.
  rewrite /COND.
  case Hc : (eqStar x 'NIL).
  - admit.
  - done.
Admitted.

Lemma cons_car_cdr (x : star) :
  ATOM x = 'NIL -> (CONS (CAR x) (CDR x)) = x.
Proof.
  intros Hn.
  case Hc: x; rewrite /CONS => /=.
  - by rewrite Hc in Hn.                    (* 前提の矛盾 *)
  - by [].
Qed.

(* **** *)

Goal forall x,  x = 'NIL -> COND x 'T 'T = 'T.
Proof.
  intros.
  Check if_nest_E.                          (* 条件付き書き換えの使い方。 *)
  rewrite if_nest_E.
  + done.
  + done.
Qed.

(* END *)
