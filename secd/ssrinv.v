From mathcomp Require Import all_ssreflect.

(* ---------------------------------------------------------------------- *)
(* ** Position markers *)
(** ** ポジションマーカ *)

(* [ltac_Mark] and [ltac_mark] are dummy definitions used as sentinel
    by tactics, to mark a certain position in the context or in the goal. *)
(** [ltac_Mark]と[ltac_mark]は、コンテキストまたはゴールにおいて、
    特定のポジションにマークをつけるために、
    タクティックが使う標識のダミーの定義です。*)

Inductive ltac_Mark : Type :=
  | ltac_mark : ltac_Mark.

(* [gen_until_mark] repeats [generalize] on hypotheses from the
    context, starting from the bottom and stopping as soon as reaching
    an hypothesis of type [Mark]. If fails if [Mark] does not
    appear in the context. *)
(** [gen_until_mark]はコンテキストの一番下の仮定から型[Mark]の仮定に逹するまで
    [generalize]を繰り返します。
    コンテキストに[Mark]が現れないときは失敗します。 *)

Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end.

(* [intro_until_mark] repeats [intro] until reaching an hypothesis of
    type [Mark]. It throws away the hypothesis [Mark].
    It fails if [Mark] does not appear as an hypothesis in the
    goal. *)
(** [intro_until_mark]は型[Mark]の仮定に逹するまで[intro]を繰り返します。
    そしてその仮定[Mark]を廃棄します。
    ゴールの仮定に[Mark]が現れないときには失敗します。 *)

Ltac intro_until_mark :=
  match goal with
  | |- (ltac_Mark -> _) => intros _
  | _ => intro; intro_until_mark
  end.


(* ********************************************************************** *)
(* * Inversion *)
(** * 反転(Inversion) *)

(** [invert keep H] は [inversion H] と同様ですが、
    得られた事実をすべてゴールに置く点が違います。キーワード[keep]
    は仮定[H]を除去しないでおくことを意味します。 *)

Tactic Notation "invert" "keep" hyp(H) :=
  pose ltac_mark; inversion H; gen_until_mark.

(* ********************************************************************** *)
(* ********************************************************************** *)

(* !! NEW !! *)

(* subst を行ってから、残った前提を generalize する。 *)
Tactic Notation "inv:" hyp(H) :=
  pose ltac_mark; inversion H; subst; gen_until_mark; clear H.

Tactic Notation "inv" :=
  let H := fresh in intro H; inv: H.

Tactic Notation "invs:" hyp(H) :=
  pose ltac_mark; inversion H; subst; try done; gen_until_mark; clear H.

Tactic Notation "invs" :=
  let H := fresh in intro H; invs: H.

(*
Tactic Notation "inv:" hyp(H) simple_intropattern(I1) :=
  generalize I1;
  inv: H.

Tactic Notation "inv:" hyp(H)
       simple_intropattern(I1) simple_intropattern(I2) :=
  generalize I2; generalize I1;
  inv: H.

Tactic Notation "inv:" hyp(H)
       simple_intropattern(I1) simple_intropattern(I2) simple_intropattern(I3) :=
  generalize I3; generalize I2; generalize I1;
  inv: H.
*)

(* END *)
