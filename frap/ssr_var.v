From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Module Literal.
  
  Inductive Literal := a | b | c | f | g | h | x | y | z.
  
  Definition eqLiteral (x y : Literal) :=
    match (x, y) with
    | (a, a) => true
    | (b, b) => true
    | (c, c) => true
    | (f, f) => true
    | (g, g) => true
    | (h, h) => true
    | (x, x) => true
    | (y, y) => true
    | (z, z) => true
    | _ => false
    end.
  
  Lemma Literal_eqP (x y : Literal) : reflect (x = y) (eqLiteral x y).
  Proof.
    rewrite /eqLiteral.
      by apply: (iffP idP); case: x; case: y.
  Qed.
  
  Definition Literal_eqMixin := EqMixin Literal_eqP.
  Canonical Literal_eqType := EqType Literal Literal_eqMixin.
  
  Definition Literal_enum := [:: a; b; c; f; g; h; x; y; z].

  Definition Literal_pickle (x : Literal_eqType) : nat :=
    match x with
    | a => 0
    | b => 1
    | c => 2
    | f => 3
    | g => 4
    | h => 5
    | x => 6
    | y => 7
    | z => 8
    end.
  
  Definition Literal_unpickle (n : nat) : option Literal_eqType :=
    match n with
    | 0 => Some a
    | 1 => Some b
    | 2 => Some c
    | 3 => Some f
    | 4 => Some g
    | 5 => Some h
    | 6 => Some x
    | 7 => Some y
    | 8 => Some z
    | _ => None
    end.

  Lemma Literal_pcancel : pcancel Literal_pickle Literal_unpickle.
  Proof.
    by case.
  Qed.
  
  Lemma Literal_finiteP (x : Literal_eqType)  :
    (count_mem x) Literal_enum = 1.
  Proof.
    by case: x.
  Qed.

  Lemma Literal_uniq : uniq Literal_enum.
  Proof.
    done.
  Qed.
  (* UniqFinMixin に使えるはずだが。。。 *)
  
End Literal.

Definition Literal_eqMixin := EqMixin Literal.Literal_eqP.
Canonical Literal_eqType := EqType Literal.Literal Literal_eqMixin.
Canonical Literal_eqType' := [eqType of Literal.Literal].

Definition Literal_countMixin := CountMixin Literal.Literal_pcancel.
Definition Literal_choiceMixin := CountChoiceMixin Literal_countMixin.

Canonical Literal_choiceType := ChoiceType Literal.Literal Literal_choiceMixin.
Canonical Literal_countType := CountType Literal_choiceType Literal_countMixin.

Definition Literal_finMixin :=
  @FinMixin Literal_countType Literal.Literal_enum Literal.Literal_finiteP.
Canonical Literal_finType := FinType Literal.Literal Literal_finMixin.

(* ちゃんと定義できていことを確認する。 *)
Check Literal_eqType : eqType.
Check Literal_choiceType : choiceType.
Check Literal_countType : countType.
Check Literal_finType : finType.

Notation Literal := Literal.Literal.        (* !!!!! *)

(* END *)
