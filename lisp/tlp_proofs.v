From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Require Import Ascii.
Require Import String.
Require Import ssr_string.
Require Import tlp_lisp_3.

Notation "'T" := (S_ATOM (ATOM_SYM "T")).
Notation "'NIL" := (S_ATOM (ATOM_SYM "NIL")).
Notation "'FOO" := (S_ATOM (ATOM_SYM "FOO")).
Notation "'BAR" := (S_ATOM (ATOM_SYM "BAR")).
Notation "'BAZ" := (S_ATOM (ATOM_SYM "BAZ")).
Notation "'?" := (S_ATOM (ATOM_SYM "?")).

(* Chapter 3 *)

Definition PAIR (x y : star) := (CONS x (CONS y 'NIL)).

Definition FIRST_OF (x : star) := (CAR x).

Definition SECOND_OF (x : star) := (CAR (CDR x)).

Theorem first_of_pair (a b : star) : (EQUAL (FIRST_OF (PAIR a b)) a).
Proof.
    by rewrite equal_same.
Qed.

Theorem second_of_pair (a b : star) : (EQUAL (SECOND_OF (PAIR a b)) b).
Proof.
    by rewrite equal_same.
Qed.

Definition IN_PAIR_P (xs : star) :=
  (_IF (EQUAL (FIRST_OF xs) '?) 'T (EQUAL (SECOND_OF xs) '?)).

Theorem in_first_of_pair (b : star) : (EQUAL (IN_PAIR_P (PAIR '? b)) 'T).
Proof.
    by rewrite equal_same.
Qed.

Theorem in_second_of_pair (a : star) : (EQUAL (IN_PAIR_P (PAIR a '?)) 'T).
Proof.
    by rewrite if_same.
Qed.
