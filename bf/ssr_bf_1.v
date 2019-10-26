(** Brainfuck *)
(** @suharahiromicihi *)
(** 2019_10_26 *)

From mathcomp Require Import all_ssreflect.
Require Import ssrinv ssrclosure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive type : Set :=
| tn
| tb
.

Inductive value : Set :=                    (* v *)
| vn (n : nat)
| vb (b : bool)
.
Coercion vn : nat >-> value.
Coercion vb : bool >-> value.

Inductive inst : Set :=                     (* c *)
| iseq (cs : seq inst)
| idrop
.

Definition cstack := seq inst.              (* c :: cs *)
Definition vstack := seq value.             (* v :: vs *)
Definition env := (vstack * cstack)%type.   (* e *)

(* brainfuck をエラーなしの small-step で実現するための準備 *)
Inductive step : relation env :=            (* env -> env -> Prop *)
| stepseq vs cs1 cs2 cs : cs1 ++ cs2 = cs ->
                           step (vs, iseq cs1 :: cs2)      (vs, cs)
| stepdrop_cons v vs cs :  step (v :: vs, idrop :: cs)     (vs, cs)
| stepdrop_nil  cs :       step ([::],    idrop :: cs)     ([::], cs)
| step_nil vs :            step (vs , [::]) (vs, [::])
.

Hint Constructors step.
Hint Constructors refl_step_closure.

Definition steprec := refl_step_closure step. (* env -> env -> Prop *)

Infix "|=>" := step (at level 50, no associativity).
Infix "|=>*" := steprec (at level 50, no associativity).

Lemma steprsc_refl (e : env) : e |=>* e.
Proof. done. Qed.

Lemma steprsc_refl' (e1 e2 : env) : e1 = e2 -> e1 |=>* e2.
Proof. by move=> <-. Qed.

Lemma steprsc_step' (e1 e2 : env) : e1 |=> e2 -> e1 |=>* e2.
Proof. by apply: rsc_R. Qed.

Lemma steprsc_step (e1 e2 e3 : env) : e1 |=> e2 -> e2 |=>* e3 -> e1 |=>* e3.
Proof. by apply: rsc_step. Qed.

Lemma steprsc_trans (e1 e2 e3 : env) : e1 |=>* e2 -> e2 |=>* e3 -> e1 |=>* e3.
Proof. by apply: rsc_trans. Qed.

(* ************* *)
(* step の決定性 *)
(* ************* *)
(* エラーがなく、かならずステップする場合の実験 *)
Theorem decide_step (e1 : env) : exists (e2 : env), e1 |=> e2.
Proof.
  case: e1.
  move=> vs cs.
  case: cs => [|c cs].
  - by exists (vs, [::]).
  - case: c.
    + move=> cs'.
      exists (vs, cs' ++ cs).
        by apply: stepseq.
    + case: vs => [|v vs].
      * exists ([::], cs).
        by apply: stepdrop_nil.
      * exists (vs, cs).
          by apply: stepdrop_cons.
Defined.                                    (* XXXX *)

(***********************)
(* 自動証明 ************)
(***********************)

Ltac stepstep_0 e1 e2 :=
  match eval hnf in (decide_step e1) with
  | (ex_intro _ _ ?p) => apply: (steprsc_step p)
  end.
Check ex_intro.
(* ex_intro P x H の
   P = (fun e2 : env => e1 |=> e2)
   x = e2
   H : e1 |=> e2、なる 命題
*)

Ltac stepstep :=
  match goal with
  | |- ?e1 |=>* ?e2 => stepstep_0 e1 e2
  end.

Definition sample :=
  [::idrop;
     idrop].


Goal ([:: vn 1], sample) |=>* ([::], [::]).
Proof.
  do !stepstep.
  (* これが、無限ループにならないのはなぜだろう。 *)
  done.
Qed.


Variable H1 : ([:: vn 1], [:: idrop; idrop]) |=> ([::], [:: idrop]).
Variable H2 : ([::], [:: idrop]) |=> ([::], [::]).
Variable H3 : ([::], [::]) |=> ([::], [::]).

Goal ([:: vn 1], sample) |=>* ([::], [::]).
Proof.
  Check exists e2 : env, ([:: vn 1], sample) |=> e2.
  Check ex_intro (fun e2 : env => ([:: vn 1], [:: idrop; idrop]) |=> e2)
        ([::], [:: idrop])
        H1.
  apply: (steprsc_step H1).
  
  Check ex_intro (fun e2 : env => ([::], [:: idrop]) |=> e2)
        ([::], [::])       
        H2.
  apply: (steprsc_step H2).

  Check ex_intro (fun e2 : env => ([::], [::]) |=> e2)
        ([::], [::])
        H3.
  apply: (steprsc_step H3).                 (* もう、進まない。 *)
  done.
Qed.

(* END *)
