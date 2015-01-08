(** 二項関係「<」が整礎であることの証明 *)
(* 2015_01_08 @suharahiromichi *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
Require Import div prime.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* well_founded の引数は Prop である必要がある。
コアーションが効いて (n < m) = true になる。
だから、well_founded ltn ではだめである。 *)
Lemma well_founded_ltn : well_founded (fun n m => n < m).
Proof.
  move=> x.
  elim: x {1 3}x (leqnn x) => [| n IHn] x H; apply: Acc_intro.
  - by case: x H.
  - by move=> y H0; apply/IHn/(leq_trans H0 H).
Defined.

(** Prop の場合は、lt_wf として定理があるが、自分で証明してみる。 *)
Search well_founded.

Require Import Arith.                       (* Lt *)
(* Coq/Arith/ の定理を使っている。 *)

Lemma well_founded_lt : well_founded lt.
Proof.
  move=> x.
  elim: x {1 3}x (le_refl x) => [| n IHn] x H; apply: Acc_intro.
  - case: x H => [|x] H1 x' H2.
    + by inversion H2.
    + exfalso.
      apply le_not_lt in H1.
      apply H1.
      by apply lt_0_Sn.
  - move=> y H0.
    apply IHn.
    apply lt_n_Sm_le.
    by apply (lt_le_trans y x n.+1 H0 H).
Defined.

(* END *)
