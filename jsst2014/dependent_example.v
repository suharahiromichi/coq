Require Import ssreflect.

(* NB : exo7 and exo8 from the JFR tutorial *)

Lemma exo7 (P : nat -> Prop) : ~ (exists x, P x) -> forall x, ~ P x.
Proof.
  move=> H x Px.
  apply: H.
  exists x.
  by [].
Qed.

Lemma exo8 (A : Prop) (P : nat -> Prop) : 
  (exists x, A -> P x) -> (forall x, ~ P x) -> ~ A.
Proof.
  move=> H notPx Ha.
  case: H => n HaPn.
  by apply/(notPx n)/HaPn/Ha.
Qed.

Lemma exo9 : 
  (exists P : nat -> Prop, forall n, P n) -> 
  forall n, exists P : nat -> Prop , P n.
Proof.
  move=> H m.
  case: H => Hm Hnm.
  exists Hm.
  by apply: Hnm.
Qed.

Require Import ssrfun ssrbool eqtype ssrnat seq path.

Definition ordered : seq nat -> bool := sorted ltn.

Inductive map :=
| mkMap : forall s : seq (nat * bool), ordered (unzip1 s) -> map.

Inductive int (n : nat) :=
| mkInt : forall s : seq bool, size s = n -> int n.

