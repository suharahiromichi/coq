From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Section s8_5.

Inductive windrose : predArgType := N | S | E | W.
(* predArgType は p.198 の末尾参照。finType で濃度を定義するために必要である。 *)

Definition w2o w : 'I_4 :=
  match w with
  | N => inord 0
  | S => inord 1
  | E => inord 2
  | W => inord 3
  end.

Definition o2w (o : 'I_4) :=
  match val o with
  | 0 => N
  | 1 => S
  | 2 => E
  | 3 => W
  | _ => N
  end.

(* pcan という名だが、cancel 述語を使っている。 *)
Lemma pcan_wo4 : cancel w2o o2w.
Proof.
  by case; rewrite /o2w /= inordK.
Qed.

Fail Check windrose : eqType.
Fail Check windrose : choiceType.
Fail Check windrose : countType.
Fail Check windrose : finType.

(*
HB.instance Definition _ : hasDecEq windrose    := CanEqMixin pcan_wo4.
HB.instance Definition _ : hasChoice windrose   := CanChoiceMixin pcan_wo4.
HB.instance Definition _ : isCountable windrose := CanCountMixin pcan_wo4.
HB.instance Definition _ : isFinite windrose    := CanFinMixin pcan_wo4.
*)

(* こちらのほうが、よりMathComp2的である。 *)
(* cancel 述語を使っているので、can_type を使う。 *)
Check can_type : forall (T T' : Type) (f : T -> T') (g : T' -> T), cancel f g -> Type.
Check @can_type windrose 'I_4 w2o o2w pcan_wo4 : Type.

HB.instance Definition _ := Equality.copy  windrose (can_type pcan_wo4).
HB.instance Definition _ := Choice.copy    windrose (can_type pcan_wo4).
HB.instance Definition _ := Countable.copy windrose (can_type pcan_wo4).
HB.instance Definition _ := Finite.copy    windrose (can_type pcan_wo4).

Check windrose : eqType.
Check windrose : choiceType.
Check windrose : countType.
Check windrose : finType.

(* 使用例 *)

Check [finType of windrose] : finType.

Lemma ord4_is_w : cancel o2w w2o.
Proof.
  move=> x; apply: val_inj; case: x.
  by do 5! [ case=> [?|//]; first by rewrite /= inordK ].
Qed.

Goal (N != S) && (N \in windrose) && (#| windrose | == 4).
Proof.
  case: eqP => //= _; rewrite -[4]card_ord.
  rewrite -(card_image (can_inj pcan_wo4)).
  apply/eqP; apply: eq_card=> o; rewrite inE.
  by apply/imageP; exists (o2w o) => //=; rewrite ord4_is_w.
Qed.

End s8_5.

(* END *)
