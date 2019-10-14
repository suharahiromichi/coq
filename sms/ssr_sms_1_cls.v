(** Tezos' Michelson small-setp semantics *)
(** @suharahiromicihi *)
(** 2019_10_12 *)

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
| idup
| iswap
| ipush (ty : type) (v : value)
| iloop (cs : seq inst)
| idip (cs : seq inst)
| iadd
| isub
| imul
| ieq
| ineq
| iret (v : value)                           (* for idip *)
.

Definition cstack := seq inst.              (* c :: cs *)
Definition vstack := seq value.             (* v :: vs *)
Definition env := (vstack * cstack)%type.   (* e *)

Definition sample1 :=
  [::
     ipush tn 1;
     ipush tn 2;
     iadd;
     idrop
  ].

Definition fact :=
  [::
     ipush tn 1;
     ipush tn 4;
     idup;
     ineq;
     iloop [::
              idup;
              idip [:: imul];
              ipush tn 1;
              iswap;
              isub;
              idup;
              ineq
           ];
     idrop
  ].

Inductive step : relation env :=            (* env -> env -> Prop *)
| stepseq vs cs1 cs2 cs : cs1 ++ cs2 = cs ->
                           step (vs, iseq cs1 :: cs2)           (vs, cs)
| stepdrop v vs cs :       step (v :: vs, idrop :: cs)          (vs, cs)
| stepdup v vs cs :        step (v :: vs, idup :: cs)           (v :: v :: vs, cs)
| stepswap v1 v2 vs cs :   step (v2 :: v1 :: vs, iswap :: cs)   (v1 :: v2 :: vs, cs)
| steppush_n n vs cs:      step (vs, ipush tn (vn n) :: cs)     ((vn n) :: vs, cs)
| steppush_b b vs cs:      step (vs, ipush tb (vb b) :: cs)     ((vb b) :: vs, cs)
| steploop_tt vs cs1 cs2 cs : cs1 ++ cs2 = cs ->
                           step (vb true :: vs, iloop cs1 :: cs2) (vs, cs)
| steploop_ff vs cs1 cs2 : step (vb false :: vs, iloop cs1 :: cs2) (vs, cs2)
| stepdip v vs1 vs2 cs1 cs2 cs : cs1 ++ [:: iret v] ++ cs2 = cs ->
                           step (v :: vs1, idip cs1 :: cs2) (vs2, cs)
| stepadd v1 v2 v3 vs cs : v1 + v2 = v3 ->
                           step (vn v2 :: vn v1 :: vs, iadd :: cs) (vn v3 :: vs, cs)
| stepsub v1 v2 v3 vs cs : v1 - v2 = v3 ->
                           step (vn v2 :: vn v1 :: vs, isub :: cs) (vn v3 :: vs, cs)
| stepmul v1 v2 v3 vs cs : v1 * v2 = v3 ->
                           step (vn v2 :: vn v1 :: vs, imul :: cs) (vn v3 :: vs, cs)
| stepeq_tt vs cs :        step (vn 0 :: vs, ieq :: cs)     (vb true :: vs, cs)
| stepeq_ff v vs cs :      step (vn v.+1 :: vs, ieq :: cs)  (vb false :: vs, cs)
| stepneq_tt v vs cs :     step (vn v.+1 :: vs, ineq :: cs) (vb true :: vs, cs)
| stepneq_ff vs cs :       step (vn 0 :: vs, ineq :: cs)    (vb false :: vs, cs)
| stepret v vs cs:         step (vs, iret v :: cs)          (v :: vs, cs)
.

Hint Constructors step.
Hint Constructors refl_step_closure.

Definition steprec := refl_step_closure step. (* env -> env -> Prop *)

Infix "|=>" := step (at level 50, no associativity).
Infix "|=>*" := steprec (at level 50, no associativity).

Lemma steprtc_refl (e : env) : e |=>* e.
Proof. done. Qed.

Lemma steprtc_refl' (e1 e2 : env) : e1 = e2 -> e1 |=>* e2.
Proof. by move=> <-. Qed.

Lemma steprtc_step (e1 e2 : env) : e1 |=> e2 -> e1 |=>* e2.
Proof. by do !econstructor. Qed.

Lemma steprtc_cons (e1 e2 e3 : env) : e1 |=> e2 -> e2 |=>* e3 -> e1 |=>* e3.
Proof. by econstructor; eauto. Qed.

Lemma steprtc_trans (e1 e2 e3 : env) : e1 |=>* e2 -> e2 |=>* e3 -> e1 |=>* e3.
Proof. by apply: rsc_trans. Qed.

Ltac i_none := right; inv=> ?; inv; done.   (* inst の条件にあわない場合 *)

(* step が決定的であることを証明する。 *)

Theorem decide_step (e1 : env) : decidable (exists (e2 : env), e1 |=> e2).
Proof.
  case: e1 => vs cs.
  case: cs => [| c]; first i_none.
  case: c.                                 (* inst で場合分けする。 *)
  (* seq *)
  - move=> cs1 cs2.
    left.
    exists (vs, cs1 ++ cs2).                (* eexists *)
      by apply: stepseq.                    (* constructor *)
  (* drop *)
  - case: vs => [cs | v vs cs]; first i_none.
    left.
    exists (vs, cs).
      by apply: stepdrop.
  (* dup *)
  - case: vs => [cs | v vs cs]; first i_none.
    left.
    exists ([:: v, v & vs], cs).
      by apply: stepdup.
  (* swap *)
  - case: vs => [cs | v1 vs cs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    left.
    exists ([:: v2, v1 & vs], cs).
      by apply: stepswap.
  (* push *)
  - move=> ty v cs.
    case: ty; case: v; try i_none.  (* nat か bool で場合分けする。 *)
    (* nat の組み合わせ と bool の組み合わせ以外を try i_none で片付ける。 *)
    + move=> n.
      left.
      exists ([:: vn n & vs], cs).
        by apply: steppush_n.
    + move=> b.
      left.
      exists ([:: vb b & vs], cs).
        by apply: steppush_b.
  (* loop *)
  - case: vs => [cs | v vs cs1 cs2]; first i_none.
    case: v => [n | b]; first i_none. (* nat か bool で場合分けする。 *)
    left.
    case: b.                      (* true か false で場合分けする。 *)
    + exists (vs, cs1 ++ cs2).
        by apply: steploop_tt.
    + exists (vs, cs2).
        by apply: steploop_ff.
        
  (* dip *)
  - case: vs => [cs1 cs2 |v vs cs1 cs2]; first i_none.
    left.
    exists (vs, cs1 ++ [:: iret v] ++ cs2). (* iret を使う例。 *)
        by apply: stepdip.
        
  (* add *)
  - case: vs => [cs | v1 vs cs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    case: v1; case: v2 => n1 n2; try i_none. (* nat か bool で場合分けする。 *)
    (* nat と nat の組み合わせ以外を try i_none で片付ける。 *)
    left.
    exists (vn (n1 + n2) :: vs, cs).
      by apply: stepadd.
  (* sub *)
  - case: vs => [cs | v1 vs cs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    case: v1; case: v2 => n1 n2; try i_none.
    left.
    exists (vn (n1 - n2) :: vs, cs).
      by apply: stepsub.
  (* mul *)
  - case: vs => [cs | v1 vs cs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    case: v1; case: v2 => n1 n2; try i_none.
    left.
    exists (vn (n1 * n2) :: vs, cs).
      by apply: stepmul.
  (* eq *)
  - case: vs => [cs | v vs cs]; first i_none.
    case: v => n; try i_none.       (* nat か bool で場合分けする。 *)
    left.
    case: n.                        (* 0 か 非0 で場合分けする。 *)
    + exists ([:: vb true & vs], cs).
        by apply: stepeq_tt.
    + exists ([:: vb false & vs], cs).
        by apply: stepeq_ff.
  (* neq *)
  - case: vs => [cs | v vs cs]; first i_none.
    case: v => n; try i_none.
    left.
    case: n.
    + exists ([:: vb false & vs], cs).
        by apply: stepneq_ff.
    + exists ([:: vb true & vs], cs).
        by apply: stepneq_tt.
        
  (* ret 追加 *)
  - move=> v cs.
    left.
    exists ([:: v & vs], cs).
      by apply: stepret.
Qed.

(* END *)
