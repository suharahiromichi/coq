From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive star (T : Type) : Type :=
| S_NIL
| S_ATOM of T
| S_CONS of star T & star T.

Fixpoint eqStar {T : eqType} (x y : star T) : bool :=
  match (x, y) with
  | (S_NIL, S_NIL) => true
  | (S_ATOM a, S_ATOM b) => (a == b :> T)   (* eqType *)
  | (S_CONS x1 y1, S_CONS x2 y2) => eqStar x1 x2 && eqStar y1 y2
  | _ => false
  end.

Lemma eqCons {T : eqType} (x y x' y' : star T) :
  (x = x' /\ y = y') -> @S_CONS T x y = @S_CONS T x' y'.
Proof.
  case=> Hx Hy.
    by rewrite Hx Hy.
Qed.

Lemma star_eqP (T : eqType) (x y : star T) : reflect (x = y) (eqStar x y).
Proof.
  apply: (iffP idP).
  - elim: x y.
    + by elim.
    + move=> x'.
      elim=> y //=.
        by move/eqP => <-.
    + move=> x Hx y Hy.
      elim=> //=.
      move=> x' IHx y' IHy /andP.
      case=> Hxx' Hyy'.
      apply: eqCons.
      split.
      * by apply: (Hx x').
      * by apply: (Hy y').
  -  move=> <-.
     elim: x => //=.
     * move=> x Hx y' Hy /=.
         by apply/andP; split.
Qed.

Definition star_eqMixin (T : eqType) := EqMixin (@star_eqP T).
Canonical star_eqType (T : eqType) := EqType (star T) (star_eqMixin T).

Arguments S_NIL [T].

(* END *)
