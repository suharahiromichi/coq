(* 7. Hierarchies *)
(* 7.5 Linking a custom data type to the library *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing Coercions.                     (* *** *)

Inductive windrose : predArgType := N | S | E | W.
Check N \in windrose.
Fail Check N != S.
Fail Check #| windrose | == 4.

Definition w2o (w : windrose) : 'I_4 :=
  match w with
  | N => inord 0
  | S => inord 1
  | E => inord 2
  | W => inord 3
  end.

Definition o2w (o : 'I_4) : windrose :=
  match val o with
  | 0 => N
  | 1 => S
  | 2 => E
  | _ => W
  end.

(* w2o と o2w がキャンセルの関係であることを証明する。 *)
Lemma can_wo4 : cancel w2o o2w.
Proof.
  case.
  rewrite /o2w.
  rewrite /val.
  rewrite /=.
  rewrite inordK.
  - done.
  - done.
  Restart.
    by case; rewrite /o2w /= inordK.
Qed.
Definition windrose_eqMixin := CanEqMixin can_wo4.

(* w2o が injective であることを証明する。 *)

Lemma inj_w2o : injective w2o.
Proof.
  Check can_inj : forall (rT aT : Type) (f : aT -> rT) (g : rT -> aT),
    cancel f g -> injective f.
  apply can_inj with (g:=o2w).              (* cancel (f:=w2o) (g:=o2w) *)
  by apply can_wo4.
Qed.
Definition windrose_eqMixin' := InjEqMixin inj_w2o.

(* Equality.axiom (∀x y, w2o x == w2o y) が成立することを証明する。 *)

Lemma w2o_eqP : Equality.axiom (fun x y => w2o x == w2o y).
Proof.
  Check inj_eqAxiom : forall (T : Type) (eT : eqType) (f : T -> Equality.sort eT),
    injective f -> Equality.axiom (T:=T) (fun x y : T => f x == f y).
  apply: inj_eqAxiom.
    by apply: inj_w2o.
Qed.
Definition windrose_eqMixin'' := EqMixin w2o_eqP.


(* Definition windrose_eqMixin := CanEqMixin can_wo4. *)
Canonical windrose_eqType := EqType windrose windrose_eqMixin.

Check N \in windrose.
Check N != S.
Fail Check #| windrose | == 4.

Definition windrose_choiceMixin := CanChoiceMixin can_wo4.
Canonical windrose_choiceType := ChoiceType windrose windrose_choiceMixin.

Definition windrose_countMixin := CanCountMixin can_wo4.
Canonical windrose_countType := CountType windrose windrose_countMixin.

Lemma windrose_enumP : Finite.axiom (undup (map o2w (Finite.enum (ordinal_finType 4)))).
Proof.
  Admitted.                                 (* XXXX *)
Definition windrose_finMixin := FinMixin windrose_enumP.

(* Definition windrose_finMixin := CanFinMixin can_wo4. *)
Canonical windrose_finType := FinType windrose windrose_finMixin.

Check N \in windrose.
Check N != S.
Check #| windrose | == 4.

(* END *)

Print Equality.axiom.
(* 一般に injective なら Equality.axiom が成り立つという定理： inj_eqAxiom *)
Check inj_eqAxiom : forall (T : Type) (eT : eqType) (f : T -> eT),
    injective f -> Equality.axiom (T:=T) (fun x y : T => f x == f y).
Check @inj_eqAxiom
      windrose                              (* T : Type *)
      (ordinal_eqType 4)                    (* eT : eqType *)
      w2o.                                  (* T -> eT *)

Print Finite.axiom.
(* 一般に cancel なら Finite.axiom が成り立つという定理 *)
Check pcan_enumP : forall (eT : countType)  (* windrose *)
                          (fT : finType)    (* 'I_4 *)
                          (f : eT -> fT) (* w2o : windrose -> 'I_4. *)
                          (g : fT -> option eT), (* o2w' : 'I_4 -> option windrose. *)
    pcancel f g -> Finite.axiom (T:=eT) (undup (pmap g (Finite.enum fT))).
(*
Check @pcan_enumP
      windrose_countType
      (ordinal_finType 4)
      w2o
      o2w.
*)

(* その他の補題 *)
Check can_pcan : forall (rT aT : Type) (f : aT -> rT) (g : rT -> aT),
    cancel f g -> pcancel f (fun y : rT => Some (g y)).

Definition o2n (o : 'I_4) : nat := val o.

(* サブタイプ型の値からオリジナル型の値を取り出す。 *)
Check @val : forall (T : Type) (P : pred T) (s : subType P), s -> T.
(* これは、injective である。 *)
Check val_inj.

(* サブタイプ('I_4 から、オリジナルタイプの nat を取り出す。 *)
Goal injective o2n.
Proof.
  move=> n x.
  rewrite /o2n.
  (* val n = val x -> n = x *)
  by apply val_inj.
Qed.

(* END *)

(* 主役は w2o か o2w か *)
(* cancel -> pcancel を使う *)
