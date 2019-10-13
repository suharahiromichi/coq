(** Tezos' Michelson small-setp semantics *)

From mathcomp Require Import all_ssreflect.
Require Import ssrinv ssrclosure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive type : Set :=
| tn
| tb
.

Inductive data : Set :=
| dn (n : nat)
| db (b : bool)
.

Inductive inst : Set :=
| iseq (i : seq inst)
| idrop
| idup
| iswap
| ipush (ty : type) (d : data)
| iloop (cs : seq inst)
| idip (cs : seq inst)
| iadd
| isub
| imul
| ieq
| ineq
| iret (d : data)                           (* for idip *)
.

Definition sample1 :=
  [::
     ipush tn (dn 1);
     ipush tn (dn 2);
     iadd;
     idrop
  ].

Definition fact :=
  [::
     ipush tn (dn 1);
     ipush tn (dn 4);
     idup;
     ineq;
     iloop [::
              idup;
              idip [:: imul];
              ipush tn (dn 1);
              iswap;
              isub;
              idup;
              ineq
           ];
     idrop
  ].

Definition cstack := seq inst.              (* i :: cs *)
Definition vstack := seq data.              (* d :: vs *)

Definition env := (vstack * cstack)%type.

Inductive eval : relation env :=            (* env -> env -> Prop *)
| evalseq  vs cs1 cs2 cs : cs1 ++ cs2 = cs ->
                           eval (vs, iseq cs1 :: cs2)           (vs, cs)
| evaldrop d vs cs :       eval (d :: vs, idrop :: cs)          (vs, cs)
| evaldup  d vs cs :       eval (d :: vs, idup :: cs)           (d :: d :: vs, cs)
| evalswap d1 d2 vs cs :   eval (d2 :: d1 :: vs, iswap :: cs)   (d1 :: d2 :: vs, cs)
| evalpush ty d vs cs:     eval (vs, ipush ty d :: cs)          (d :: vs, cs)
| evalloop_tt vs cs1 cs2 cs : cs1 ++ cs2 = cs ->
                           eval (db true :: vs, iloop cs1 :: cs2) (vs, cs)
| evalloop_ff vs i cs :    eval (db false :: vs, iloop i :: cs) (vs, cs)
| evaldip d vs1 vs2 cs1 cs2 cs : cs1 ++ [:: iret d] ++ cs2 = cs -> (* XXX *)
                           eval (d :: vs1, idip cs1 :: cs2) (vs2, cs)
| evaladd d1 d2 d3 vs cs : d1 + d2 = d3 ->
                           eval (dn d2 :: dn d1 :: vs, iadd :: cs) (dn d3 :: vs, cs)
| evalsub d1 d2 d3 vs cs : d1 - d2 = d3 ->
                           eval (dn d2 :: dn d1 :: vs, isub :: cs) (dn d3 :: vs, cs)
| evalmul d1 d2 d3 vs cs : d1 * d2 = d3 ->
                           eval (dn d2 :: dn d1 :: vs, imul :: cs) (dn d3 :: vs, cs)
| evaleq_tt vs cs :        eval (dn 0 :: vs, ieq :: cs)     (db true :: vs, cs)
| evaleq_ff d vs cs :      eval (dn d.+1 :: vs, ieq :: cs)  (db false :: vs, cs)
| evalneq_tt d vs cs :     eval (dn d.+1 :: vs, ineq :: cs) (db true :: vs, cs)
| evalneq_ff vs cs :       eval (dn 0 :: vs, ineq :: cs)    (db false :: vs, cs)
| evalret  d vs cs:        eval (vs, iret d :: cs)          (d :: vs, cs)
.

Hint Constructors eval.
Hint Constructors refl_step_closure.

Definition evalrec := refl_step_closure eval. (* env -> env -> Prop *)

Infix "|=>" := eval (at level 50, no associativity).
Infix "|=>*" := evalrec (at level 50, no associativity).

Lemma evalrtc_refl (e : env) : e |=>* e.
Proof. done. Qed.

Lemma evalrtc_refl' (e1 e2 : env) : e1 = e2 -> e1 |=>* e2.
Proof. by move=> <-. Qed.

Lemma evalrtc_step (e1 e2 : env) : e1 |=> e2 -> e1 |=>* e2.
Proof. by do !econstructor. Qed.

Lemma evalrtc_cons (e1 e2 e3 : env) : e1 |=> e2 -> e2 |=>* e3 -> e1 |=>* e3.
Proof. by econstructor; eauto. Qed.

Lemma evalrtc_trans (e1 e2 e3 : env) : e1 |=>* e2 -> e2 |=>* e3 -> e1 |=>* e3.
Proof. by apply: rsc_trans. Qed.

Theorem decide_eval (e1 : env) : decidable (exists (e2 : env), e1 |=> e2).
Proof.
  case: e1 => vs cs.
  case: cs;  [| move=> i; case: i].
  (* case=> [vs [|[]]]. *)
  
  - right=> Hc.                             (* [::] *)
    now inversion Hc.
  - move=> sc1 sc2.                         (* iseq *)
    left.
    exists (vs, sc1 ++ sc2).
    by econstructor.
  - case: vs.                               (* idrop *)
    + right=> Hc. inversion Hc. by inversion H.
    + move=> d vs sc.
      left.
        by eexists; econstructor.
  - case: vs.                               (* idup *)
    + right=> Hc. inversion Hc. by inversion H.
    + move=> d vs sc.
      left.
        by eexists; econstructor.
  - case: vs.                               (* iswap *)
    + right=> Hc. inversion Hc. by inversion H.
    + move=> d2 vs'.
      case: vs'.
      * right=> Hc. inversion Hc. by inversion H.
      * move=> d vs'.
        left.
          by eexists; econstructor. (* by exists ([:: d, d2 & vs'], cs) *)
  - move=> ty d sc.                         (* ipush *)
    left.
      by eexists; econstructor.            (* by exists (d :: vs, sc) *)
  - case: vs.                              (* iloop *)
    + right=> Hc. inversion Hc. by inversion H.
    + move=> d vs' i cs.
      case: d.
      * right=> Hc. inversion Hc. by inversion H.
      * left.
        case: b.
        -- by eexists; econstructor.
        -- by eexists; econstructor.

  - case: vs => d vs1.                      (* idip *)
    + right=> Hc. inversion Hc. by inversion H.
    + move=> sc1 sc2.
      left.
      exists (vs1, sc1 ++ [:: iret d] ++ sc2).
        by apply: evaldip.
        
  - case: vs.                               (* iadd *)
    + right=> Hc. inversion Hc. by inversion H.
    + move=> d2 vs'.
      case: vs'.
      * right=> Hc. inversion Hc. by inversion H.
      * move=> d vs'.
        case: d; case: d2.
        -- move=> n2 n1 sc.
            left.
            exists (dn (n1 + n2) :: vs', sc).
              by apply: evaladd.
        -- right=> Hc. inversion Hc. by inversion H.
        -- right=> Hc. inversion Hc. by inversion H.
        -- right=> Hc. inversion Hc. by inversion H.
  - case: vs.                               (* isub *)
    + right=> Hc. inversion Hc. by inversion H.
    + move=> d2 vs'.
      case: vs'.
      * right=> Hc. inversion Hc. by inversion H.
      * move=> d vs'.
        case: d; case: d2.
        -- move=> n2 n1 sc.
            left.
            exists (dn (n1 - n2) :: vs', sc).
              by apply: evalsub.
        -- right=> Hc. inversion Hc. by inversion H.
        -- right=> Hc. inversion Hc. by inversion H.
        -- right=> Hc. inversion Hc. by inversion H.
  - case: vs.                               (* imul *)
    + right=> Hc. inversion Hc. by inversion H.
    + move=> d2 vs'.
      case: vs'.
      * right=> Hc. inversion Hc. by inversion H.
      * move=> d vs'.
        case: d; case: d2.
        -- move=> n2 n1 sc.
            left.
            exists (dn (n1 * n2) :: vs', sc).
              by apply: evalmul.
        -- right=> Hc. inversion Hc. by inversion H.
        -- right=> Hc. inversion Hc. by inversion H.
        -- right=> Hc. inversion Hc. by inversion H.
  - case: vs.                               (* ieq *)
    + right=> Hc. inversion Hc. by inversion H.
    + case.
      * case=> vs cs.
        -- left.                            (* [:: 0 ;..... *)
           eexists.
             by apply: evaleq_tt.
        -- left.                            (* [:: 1 ; .... *)
           eexists.
             by apply: evaleq_ff.
      * right=> Hc. inversion Hc. by inversion H.
  - case: vs.                               (* ineq *)
    + right=> Hc. inversion Hc. by inversion H.
    + case.
      * case=> vs cs.
        -- left.                            (* [:: 0 ;..... *)
           eexists.
             by apply: evalneq_ff.
        -- left.                            (* [:: 1 ; .... *)
           eexists.
             by apply: evalneq_tt.
      * right=> Hc. inversion Hc. by inversion H.
  - move=> d sc.                            (* iret *)
    left.
      by eexists; econstructor.            (* by exists (d :: vs, sc) *)
Qed.

(* END *)
