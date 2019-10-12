(** Tezos' Michelson Sample Code *)
(** https://gitlab.com/nomadic-labs/mi-cho-coq/tree/master/src/michocott *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import michelson.                   (* michocott *)

Require Import ZArith.
Import ListNotations.

Notation "i1 ;; i2" := (i_Seq i1 i2) (at level 11, right associativity).

Definition sample1 :=
  i_Push (t_Ct ct_Nat) (d_Num (N_NatConstant 1));;
  i_Push (t_Ct ct_Nat) (d_Num (N_NatConstant 2));;
  i_Add;;
  i_Drop.

Goal BigStep sample1 (SE_Stack []) (SE_Stack []).
Proof.
  eapply bs_sequence.
  - apply bs_push.
  - eapply bs_sequence.
    + apply bs_push.
    + eapply bs_sequence.
      * apply bs_add.
      * apply bs_drop with (d := d_Num (N_NatConstant 3)).
Qed.

Hint Constructors BigStep.

Goal BigStep sample1 (SE_Stack []) (SE_Stack []).
Proof.
  unfold sample1.
  eauto.
Qed.

(* ******** *)
(* factrial *)
(* ******** *)

Definition fact :=
  i_Push (t_Ct ct_Int) (d_Num (N_IntConstant 1));;
  i_Push (t_Ct ct_Int) (d_Num (N_IntConstant 4));;
  i_Dup;;
  i_Neq;;
  i_Loop (
    i_Dup;;
    i_Dip (i_Mul);;
    i_Push (t_Ct ct_Int) (d_Num (N_IntConstant 1));;
    i_Swap;;
    i_Sub;;
    i_Dup;;
    i_Neq);;
  i_Drop.

Goal BigStep fact (SE_Stack []) (SE_Stack [d_Num (N_IntConstant 24)]).
Proof.
  eapply bs_sequence; [now apply bs_push |].
  eapply bs_sequence; [now apply bs_push |].
  eapply bs_sequence; [now apply bs_dup |].
  eapply bs_sequence; [now apply bs_neq_tt |].
  eapply bs_sequence.
  - apply bs_loop_tt
      with (S := [d_Num (N_IntConstant 4); d_Num (N_IntConstant 1)]).
    eapply bs_sequence.
    + eapply bs_sequence; [now apply bs_dup |].
      eapply bs_sequence; [now apply bs_dip |].
      eapply bs_sequence; [now apply bs_push |].
      eapply bs_sequence; [now apply bs_swap |].
      eapply bs_sequence; [now apply bs_sub |].
      eapply bs_sequence; [now apply bs_dup |].
      now apply bs_neq_tt.
    + apply bs_loop_tt
        with (S := [d_Num (N_IntConstant 3); d_Num (N_IntConstant 4)]).
      eapply bs_sequence.
      * eapply bs_sequence; [now apply bs_dup |].
        eapply bs_sequence; [now apply bs_dip |].
        eapply bs_sequence; [now apply bs_push |].
        eapply bs_sequence; [now apply bs_swap |].
        eapply bs_sequence; [now apply bs_sub |].
        eapply bs_sequence; [now apply bs_dup |].
        now apply bs_neq_tt.
      * apply bs_loop_tt
          with (S := [d_Num (N_IntConstant 2); d_Num (N_IntConstant 12)]).
        eapply bs_sequence.
        -- eapply bs_sequence; [now apply bs_dup |].
           eapply bs_sequence; [now apply bs_dip |].
           eapply bs_sequence; [now apply bs_push |].
           eapply bs_sequence; [now apply bs_swap |].
           eapply bs_sequence; [now apply bs_sub |].
           eapply bs_sequence; [now apply bs_dup |].
           now apply bs_neq_tt.
        -- apply bs_loop_tt
             with (S := [d_Num (N_IntConstant 1); d_Num (N_IntConstant 24)]).
           eapply bs_sequence.
           ++ eapply bs_sequence; [now apply bs_dup |].
              eapply bs_sequence; [now apply bs_dip |].
              eapply bs_sequence; [now apply bs_push |].
              eapply bs_sequence; [now apply bs_swap |].
              eapply bs_sequence; [now apply bs_sub |].
              eapply bs_sequence; [now apply bs_dup |].
              now apply bs_neq_ff.
           ++ now apply bs_loop_ff.
  - now eapply bs_drop.
Qed.

(* END *)
