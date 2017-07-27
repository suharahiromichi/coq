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
  - case: x; case: y; rewrite /eqLit => x y; move/eqP => H;
    by [rewrite H| | |rewrite H].
  - move=> H; rewrite H.
    case: y H => n H1;
    by rewrite /eqLit.
Qed.
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

Lemma eqCons x y x' y' : (x = x' /\ y = y') -> S_CONS x y = S_CONS x' y'.
Proof.
  case=> Hx Hy.
  by rewrite Hx Hy.
Qed.

Lemma star_eqP_1 : forall (x y : star), eqStar x y -> x = y.
Proof.
  elim.
  - move=> a.
    elim=> b.
    + move/eqP=> H.                         (* ATOM どうし *)
        by rewrite H.  
    + done.                                 (* ATOM と CONS *)
  - move=> x Hx y Hy.
    elim.
    + done.                                 (* CONS と ATOM *)
    + move=> x' IHx y' IHy.                 (* CONS と CONS *)
      move/andP.
      case=> Hxx' Hyy'.
      apply: eqCons.
      split.
      * by apply: (Hx x').
      * by apply: (Hy y').
Qed.

Lemma star_eqP_2 : forall (x y : star), x = y -> eqStar x y.
Proof.
  move=> x y H; rewrite -H {H}.
  elim: x.
  - by move=> a /=.
  - move=> x Hx y' Hy /=.
    by apply/andP; split.
Qed.

Lemma star_eqP : forall (x y : star), reflect (x = y) (eqStar x y).
Proof.
  move=> x y.
  apply (iffP idP).
  + by apply star_eqP_1.
  + by apply star_eqP_2.
Qed.
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

(* **** *)

(* S-EXPを論理式(Prop)に埋め込むためのコアーションを定義する。 *)
(* 否定が扱えるように、一旦boolを経由する。 *)
Coercion is_not_nil (x : star) : bool := ~~ eqStar x 'NIL.

Check (ATOM 'T) : star.
Check (ATOM 'T) : Prop.
Check ~ (ATOM 'T) : Prop.

Check (ATOM (CONS 'T 'T)) : star.
Check (ATOM (CONS 'T 'T)) : Prop.
Check ~ (ATOM (CONS 'T 'T)) : Prop.

Definition COND (q a e : star) : star :=
  if q == 'NIL then e else a.

Definition EQUAL (x y : star) : star :=
  if x == y then 'T else 'NIL.

(* *********** *)
(* J-Bobの定理 *)
(* *********** *)

Lemma atom_cons (x y : star) :
  (ATOM (CONS x y)) = 'NIL.
Proof.
  done.
Qed.

Lemma car_cons (x y : star) :
  CAR (CONS x y) = x.
Proof.
  done.
Qed.

Lemma cdr_cons (x y : star) :
  (CDR (CONS x y)) = y.
Proof.
  done.
Qed.

Lemma refl_eqStar (x : star) : (x == x).
Proof.
  by apply/eqP.
Qed.

Lemma symm_eqStar (x y : star) : (x == y) = (y == x).
Proof.
  by apply/idP/idP; move/eqP=> H; rewrite H.
Qed.

Lemma equal_same (x : star) :
  EQUAL x x.
Proof.
  elim: x.
  - move=> a.
    rewrite /EQUAL //=.
    case Hc : (S_ATOM a == S_ATOM a).
    + done.
    + by move/eqP in Hc.
  - move=> x Hxx y Hyy.
    rewrite /EQUAL //=.
    case Hc : (S_CONS x y == S_CONS x y).
    + done.
    + by move/eqP in Hc.
  Restart.
  rewrite /EQUAL.
  by rewrite refl_eqStar.
Qed.

Lemma equal_swap (x y : star) :
  EQUAL x y = EQUAL y x.
Proof.
  rewrite /EQUAL.
  by rewrite symm_eqStar.
Qed.

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
  (COND 'T x y) = x.
Proof.
  rewrite /COND.
  simpl.
  done.
Qed.

Lemma if_false (x y : star) :
  (COND 'NIL x y) = y.
Proof.
  done.
Qed.

Lemma if_nest_E (x y z : star) :
  x = 'NIL -> (COND x y z) = z.
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
  x -> (COND x y z) = y.
Proof.
  move=> H.
  rewrite /COND.
  case Hc : (x == 'NIL).
  - move/eqP in Hc.
    move/eqP in H.
    done.
  - done.
Qed.

Lemma cons_car_cdr (x : star) :
  (ATOM x) = 'NIL -> (CONS (CAR x) (CDR x)) = x.
Proof.
  intros Hn.
  case Hc: x; rewrite /CONS => /=.
  - by rewrite Hc in Hn.                    (* 前提の矛盾 *)
  - by [].
Qed.

(* ****** *)
(* SAMPLE *)
(* ****** *)

(* cons_car_cdr を使う例。 *)
Goal forall a, (COND (ATOM (CAR a)) 'T (EQUAL (CONS (CAR (CAR a)) (CDR (CAR a))) (CAR a))).
Proof.
  move=> a.
  rewrite {1}/COND.
  case Hc : (ATOM (CAR a) == 'NIL).
  - Check @cons_car_cdr (CAR a).
    rewrite (@cons_car_cdr (CAR a)).
    + Check equal_same (CAR a).             (* 定理の本体分 *)
        by apply (equal_same (CAR a)).
    + by move/eqP in Hc.                    (* 定理の条件部分 *)
  - done.                                   (* A節 *)
Qed.


(* おまけ。 *)
(* 条件にS式を埋め込む例。 *)

(* cons_car_cdr' を使う例。 *)
Lemma cons_car_cdr' (x : star) :
  ~ (ATOM x) -> (CONS (CAR x) (CDR x)) = x.
Proof.
  intros Hn.
  case Hc: x; rewrite /CONS => /=.
  - by rewrite Hc in Hn.                    (* 前提の矛盾 *)
  - by [].
Qed.

Definition COND' (q a e : star) : star :=
  if q then a else e.

Goal forall a, (COND' (ATOM (CAR a)) 'T (EQUAL (CONS (CAR (CAR a)) (CDR (CAR a))) (CAR a))).
Proof.
  move=> a.
  rewrite {1}/COND'.
  case Hc : (is_not_nil (ATOM (CAR a))).
  - done.                                   (* A節 *)
  - rewrite (@cons_car_cdr (CAR a)).
    + by rewrite  (equal_same (CAR a)).     (* 定理の本体分 *)
    + by move/eqP in Hc.                    (* 定理の条件部分 *)
Qed.


Lemma if_nest_E' (x y z : star) :
  ~ x  -> (COND x y z) = z.
Proof.
  move=> H.
  rewrite /COND.
  case Hc : (x == 'NIL).
  - done.
  - move/eqP in Hc.
    move/eqP in H.
    admit.
Admitted.


(* END *)
