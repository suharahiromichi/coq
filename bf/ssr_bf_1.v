(** Brainfuck *)
(** @suharahiromicihi *)
(** 2019_10_26 *)

From mathcomp Require Import all_ssreflect.
Require Import ssrinv ssrclosure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive inst : Set :=                     (* c *)
| ileft                                     (* < *)
| iright                                    (* > *)
| iinc                                      (* + *)
| idec                                      (* - *)
| iout                                      (* . *)
| iin                                       (* , *)
| iloop (i : seq inst)                      (* [ と ] *)
.

Definition cstack := seq inst.              (* c :: cs *)
Definition lstack := seq nat.               (* l :: ls *)
Definition rstack := seq nat.               (* r :: rs *)
Definition input := seq nat.                (* x :: ins *)
Definition output := seq nat.               (* x :: outs *)
Definition env := (cstack * lstack * nat * rstack * input * output)%type.

Inductive step : relation env :=            (* env -> env -> Prop *)
| stepdone x rs ls ins outs :
    step (         [::],     ls,     x,      rs,      ins,      outs)
         (         [::],     ls,     x,      rs,      ins,      outs)
| stepleft_z x cs rs ins outs :             (* < *)
    step (ileft   :: cs,    [::],    x,      rs,      ins,      outs)
         (           cs,    [::],    0, x :: rs,      ins,      outs)
| stepleft_v x y cs ls rs ins outs :        (* < *)
    step (ileft   :: cs, y :: ls,    x,      rs,      ins,      outs)
         (           cs,      ls,    y, x :: rs,      ins,      outs)
| stepright_z x cs ls ins outs :            (* > *)
    step (iright  :: cs,      ls,    x,    [::],      ins,      outs)
         (           cs, x :: ls,    0,    [::],      ins,      outs)
| stepright_v x y cs rs ls ins outs :       (* > *)
    step (iright  :: cs,      ls,    x, y :: rs,      ins,      outs)
         (           cs, x :: ls,    y,      rs,      ins,      outs)
| stepinc x cs rs ls ins outs :             (* + *)
    step (iinc    :: cs,      ls,    x,      rs,      ins,      outs)
         (           cs,      ls, x.+1,      rs,      ins,      outs)
| stepdec x cs rs ls ins outs :             (* - *)
    step (idec    :: cs,      ls,    x,      rs,      ins,      outs)
         (           cs,      ls, x.-1,      rs,      ins,      outs)
| stepin_z x cs rs ls outs :                (* . *)
    step (iin     :: cs,      ls,    x,      rs,     [::],      outs)
         (           cs,      ls,    0,      rs,     [::],      outs)
| stepin_v x y cs rs ls ins outs :          (* . *)
    step (iin     :: cs,      ls,    x,      rs, y :: ins,      outs)
         (           cs,      ls,    y,      rs,      ins,      outs)
| stepout x cs rs ls ins outs :             (* , *)
    step (iout    :: cs,      ls,    x,      rs,      ins,      outs)
         (           cs,      ls,    x,      rs,      ins, x :: outs)
| steploop_z c cs rs ls ins outs :          (* [ *)
    step (iloop c :: cs,      ls,    0,      rs,      ins,      outs)
         (           cs,      ls,    0,      rs,      ins,      outs)
| steploop_v x c cs rs ls ins outs :        (* ] *)
    step (iloop c :: cs,      ls, x.+1,      rs,      ins,      outs)
 (c ++  (iloop c :: cs),      ls, x.+1,      rs,      ins,      outs)         
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

Theorem decide_step (e1 : env) : exists (e2 : env), e1 |=> e2.
Proof.
  case: e1  => [[[[[cs ls] x] rs] ins] outs].
  case: cs => [|c cs].
  - by eexists; constructor.
  - case: c.
    + case: ls => [|x' ls']; by eexists; constructor.   (* < *)
    + case: rs => [|x' rs']; by eexists; constructor.   (* > *)
    + by eexists; constructor.                          (* + *)
    + by eexists; constructor.                          (* - *)
    + by eexists; constructor.                          (* , *)
    + case: ins => [|x' ins']; by eexists; constructor. (* . *)
    + move=> cs'.
      case: x => [| x']; by eexists; constructor. (* [ と ] *)
Defined.

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
  [:: ileft;
     iinc;
     ileft].

Goal (sample, [::], 0, [::], [::], [::]) |=>*
     ([::],   [::], 0, [:: 1; 0], [::], [::]).
Proof.
  do !stepstep.
  (* これが、無限ループにならないのはなぜだろう。 *)
  done.
Qed.

(*
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
*)

(* END *)
