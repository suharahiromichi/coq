From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Require Import Ascii.
Require Import String.
Require Import ssr_string.
Require Import tlp_lisp_3.
Require Import Coq.Program.Wf.

Notation "'T" := (S_ATOM (ATOM_SYM "T")).
Notation "'NIL" := (S_ATOM (ATOM_SYM "NIL")).
Notation "'FOO" := (S_ATOM (ATOM_SYM "FOO")).
Notation "'BAR" := (S_ATOM (ATOM_SYM "BAR")).
Notation "'BAZ" := (S_ATOM (ATOM_SYM "BAZ")).
Notation "'?" := (S_ATOM (ATOM_SYM "?")).

(* Chapter 3 *)

Definition PAIR x y := (CONS x (CONS y 'NIL)).

Definition FIRST_OF x := (CAR x).

Definition SECOND_OF x := (CAR (CDR x)).

Theorem first_of_pair a b : (EQUAL (FIRST_OF (PAIR a b)) a).
Proof.
    by rewrite equal_same.
Qed.

Theorem second_of_pair a b : (EQUAL (SECOND_OF (PAIR a b)) b).
Proof.
    by rewrite equal_same.
Qed.

Definition IN_PAIR_P xs :=
  (_IF (EQUAL (FIRST_OF xs) '?) 'T (EQUAL (SECOND_OF xs) '?)).

Theorem in_first_of_pair b : (EQUAL (IN_PAIR_P (PAIR '? b)) 'T).
Proof.
    by rewrite equal_same.
Qed.

Theorem in_second_of_pair a : (EQUAL (IN_PAIR_P (PAIR a '?)) 'T).
Proof.
    by rewrite if_same.
Qed.

Definition LIST0P x := (EQUAL x 'NIL).

Definition LIST1P x := (_IF (ATOM x) 'NIL (LIST0P (CDR x))).

Definition LIST2P x := (_IF (ATOM x) 'NIL (LIST1P (CDR x))).

(* partial は定義できない。 *)

Program Fixpoint LISTP (x : star) {measure (s_size x)} : star :=
  (_IF (ATOM x) (EQUAL x 'NIL) (LISTP (CDR x))).
Obligation 1.
Proof.
  apply/ltP.
  apply l_size_cdr.
  (* ATOM x = 'NIL *)
Admitted.

Compute (LISTP 'T).                           (* 'NIL *)
Compute (LISTP 'NIL).                         (* 'T *)
Compute (LISTP (CONS 'FOO (CONS 'FOO 'NIL))). (* 'T *)

Program Fixpoint SUB (x y : star) {measure (s_size y)} : star :=
  (_IF (ATOM y) (_IF (EQUAL y '?) x y) (CONS (SUB x (CAR y)) (SUB x (CDR y)))).
Obligation 1.
Proof.
  apply/ltP.
  apply l_size_car.
Admitted.
Obligation 2.
Proof.
  apply/ltP.
  apply l_size_cdr.
Admitted.

Compute (SUB 'FOO (CONS 'BAR (CONS '? 'NIL))). (* S_CONS 'BAR (S_CONS 'FOO 'NIL) *)

(* Chapter 5 *)

Program Fixpoint MEMBP (xs : star) {measure (s_size xs)} : star :=
  (_IF (ATOM xs) 'NIL (_IF (EQUAL (CAR xs) '?) 'T (MEMBP (CDR xs)))).
Obligation 1.
Proof.
  apply/ltP.
  apply l_size_cdr.
Admitted.

Program Fixpoint REMB (xs : star) {measure (s_size xs)} : star :=
  (_IF (ATOM xs)
       'NIL
       (_IF (EQUAL (CAR xs) '?) (REMB (CDR xs)) (CONS (CAR xs) (REMB (CDR xs))))).
Obligation 1.
Proof.
  apply/ltP.
  apply l_size_cdr.
Admitted.
Obligation 2.
Proof.
  apply/ltP.
  apply l_size_cdr.
Admitted.

Compute (REMB (CONS 'FOO (CONS '? (CONS 'BAR 'NIL)))). (* S_CONS 'FOO (S_CONS 'BAR 'NIL) *)

Theorem membp_remb0 : (EQUAL (MEMBP (REMB 'NIL)) 'NIL).
Proof.
  done.
Qed.

Theorem membp_remb1 x1 : (EQUAL (MEMBP (REMB (CONS x1 'NIL))) 'NIL).
Proof.
Admitted.

(* END *)


