(* 7. Hierarchies *)
(* 7.5 Linking a custom data type to the library *)

From mathcomp Require Import all_ssreflect.

(* Inductive windrose : Type := N | S | E | W. *)
Inductive windrose : predArgType := N | S | E | W.

Definition w2o (w : windrose) : 'I_4 :=
  match w with
  | N => inord 0
  | S => inord 1
  | E => inord 2
  | W => inord 3
  end.

Definition o2w (o : 'I_4) : option windrose :=
  match val o with
  | 0 => Some N
  | 1 => Some S
  | 2 => Some E
  | 3 => Some W
  | _ => None
  end.

Lemma pcan_wo4 : pcancel w2o o2w.
Proof.
    by case; rewrite /o2w /= inordK.
Qed.

Definition windrose_eqMixin := PcanEqMixin pcan_wo4.
Canonical windrose_eqType := EqType windrose windrose_eqMixin.
Definition windrose_choiceMixin := PcanChoiceMixin pcan_wo4.
Canonical windrose_choiceType := ChoiceType windrose windrose_choiceMixin.
Definition windrose_countMixin := PcanCountMixin pcan_wo4.
Canonical windrose_countType := CountType windrose windrose_countMixin.
Definition windrose_finMixin := PcanFinMixin pcan_wo4.
Canonical windrose_finType := FinType windrose windrose_finMixin.

(* predArgType にしないとエラーになる。 *)
Check (N != S) && (N \in windrose) && (#| windrose | == 4).

(* END *)
