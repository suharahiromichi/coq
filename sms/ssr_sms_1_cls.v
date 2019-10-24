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
| iret (v : value)                          (* for idip, internal use *)
.

Definition cstack := seq inst.              (* c :: cs *)
Definition vstack := seq value.             (* v :: vs *)
Definition env := (vstack * cstack)%type.   (* e *)

Inductive step : relation env :=            (* env -> env -> Prop *)
| stepseq vs cs1 cs2 cs : cs1 ++ cs2 = cs ->
                           step (vs, iseq cs1 :: cs2)           (vs, cs)
| stepdrop v vs cs :       step (v :: vs, idrop :: cs)          (vs, cs)
| stepdup v vs cs :        step (v :: vs, idup :: cs)           (v :: v :: vs, cs)
| stepswap v1 v2 vs cs :   step (v2 :: v1 :: vs, iswap :: cs)   (v1 :: v2 :: vs, cs)
| steppush_n n vs cs:      step (vs, ipush tn (vn n) :: cs)     ((vn n) :: vs, cs)
| steppush_b b vs cs:      step (vs, ipush tb (vb b) :: cs)     ((vb b) :: vs, cs)
| steploop_tt vs cs1 cs2 cs : cs1 ++ (iloop cs1 :: cs2) = cs ->
                           step (vb true :: vs, iloop cs1 :: cs2) (vs, cs)
| steploop_ff vs cs1 cs2 : step (vb false :: vs, iloop cs1 :: cs2) (vs, cs2)
| stepdip v vs cs1 cs2 cs : cs1 ++ (iret v :: cs2) = cs ->
                           step (v :: vs, idip cs1 :: cs2) (vs, cs)
| stepadd n1 n2 n3 vs cs : n2 + n1 = n3 ->
                           step ([:: vn n2, vn n1 & vs], iadd :: cs) (vn n3 :: vs, cs)
| stepsub n1 n2 n3 vs cs : n2 - n1 = n3 ->
                           step ([:: vn n2, vn n1 & vs], isub :: cs) (vn n3 :: vs, cs)
| stepmul n1 n2 n3 vs cs : n2 * n1 = n3 ->
                           step ([:: vn n2, vn n1 & vs], imul :: cs) (vn n3 :: vs, cs)
| stepeq_tt vs cs :        step (vn 0 :: vs, ieq :: cs)     (vb true :: vs, cs)
| stepeq_ff n vs cs :      step (vn n.+1 :: vs, ieq :: cs)  (vb false :: vs, cs)
| stepneq_tt n vs cs :     step (vn n.+1 :: vs, ineq :: cs) (vb true :: vs, cs)
| stepneq_ff vs cs :       step (vn 0 :: vs, ineq :: cs)    (vb false :: vs, cs)
| stepret v vs cs:         step (vs, iret v :: cs)          (v :: vs, cs)
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
Ltac i_none := right; inv=> ?; inv; done.   (* inst の条件にあわない場合 *)
Ltac i_done := left; eexists; constructor; done. (* inst の定義にあう場合。 *)

Theorem decide_step (e1 : env) : decidable (exists (e2 : env), e1 |=> e2).
Proof.
  case: e1 => [vs [| c cs]]; try i_none.
  case: c.                                 (* inst で場合分けする。 *)
  - move: cs => cs2 cs1; i_done.                      (* seq *)
  - case: vs => [| v vs]; try i_none; i_done.         (* drop *)
  - case: vs => [| v vs]; try i_none; i_done.         (* dup *)
  - case: vs => [| v1 [| v2 vs]]; try i_none; i_done. (* swap *)
  - case=> [] [] n; try i_none; i_done.               (* push *)
  - case: vs => [| [n | b] vs]; try i_none.
    case: b; i_done.                          (* if_tt と if_ff *)
  - case: vs => [| v vs]; try i_none. i_done. (* dip *)
  - case: vs => [| [n1 | b1] [| [n2 | b2] vs]]; try i_none; i_done. (* add *)
  - case: vs => [| [n1 | b1] [| [n2 | b2] vs]]; try i_none; i_done. (* sub *)
  - case: vs => [| [n1 | b1] [| [n2 | b2] vs]]; try i_none; i_done. (* mul *)
  - case: vs => [| [n | b] vs]; try i_none.
    case: n; i_done.                                (* eq_tt と eq_ff *)
  - case: vs => [| [n | b] vs]; try i_none.
    case: n; i_done.                                (* neq_ff と neq_tt *)
  - case: vs => [| v vs]; try i_none; i_done.       (* 追加 ret *)
Defined.

(* ************* *)
(* step の一意性 *)
(* ************* *)
Theorem step_uniqueness (e1 e2 e3 : env) :
  e1 |=> e2 -> e1 |=> e3 -> e2 = e3.
Proof.
    by inv; inv.
Qed.

(* ************** *)
(* steprc の合流性 *)
(* ************** *)
Theorem steprsc_confluence (e1 e2 e3 : env) :
  e1 |=>* e2 -> e1 |=>* e3 -> e2 |=>* e3 \/ e3 |=>* e2.
Proof.
  elim=> [e2' H2'__3 | e1' e2' e3' H1'_2' H2'3' IHe H1'__3].
  - by left.
  - inv: H1'__3.
    + right.
        by apply: (steprsc_step H1'_2' H2'3'). (* H3__3' *)
    + move=> e2'' H1'_2'' H2''_3.
      apply: IHe.
      rewrite (step_uniqueness H1'_2' H1'_2''). (* e2' = e2'' *)
        by apply: H2''_3.
Qed.
(**
 * ここで証明したのは：
 *    e1
 *  /    \
 * e2     e3
 *    →
 *    OR
 *    ←
 *
 * 本来の合流性は、これより弱い：
 *    e1
 *  /    \
 * e2     e3
 *  \    /
 *    e4
 *)
Theorem steprsc_confluence_weak (e1 e2 e3 : env) :
  e1 |=>* e2 -> e1 |=>* e3 -> (exists e4, e2 |=>* e4 /\ e3 |=>* e4).
Proof.
  move=> H1__2 H1__3.
  case: (steprsc_confluence H1__2 H1__3) => [H2__3 | H3__2].
  - exists e3.
      by split.
  - exists e2.
      by split.
Qed.

Lemma exists_and_right_map (P Q R : inst -> Prop) :
  (forall i, Q i -> R i) -> (exists i, P i /\ Q i) -> (exists i, P i /\ R i).
Proof.
    by firstorder.
Qed.

(***********************)
(* 自動証明 ************)
(***********************)

Ltac stepstep_0 e1 e2 :=
(* apply: steprsc_refl || これは使わず、done で終了する。 *)
  match eval hnf in (decide_step e1) with
  | left (ex_intro _ _ ?p) => apply: (steprsc_step p)
  end.

Ltac stepstep :=
  match goal with
  | |- ?e1 |=>* ?e2 => stepstep_0 e1 e2
  end.

(* ********** *)
(* 階乗の計算 *)
(* ********** *)
Definition fact_loop :=
  [::idup;
     ineq;
     iloop [::idup;
              idip [:: imul];
              ipush tn 1;
              iswap;
              isub;
              idup;
              ineq
           ]
  ].

Goal ([:: vn 4; vn 1], fact_loop) |=>*
     ([:: vn 0; vn 24], [::]).
Proof.
  do !stepstep.
  done.
Qed.

Goal ([:: vn 4; vn 1], fact_loop) |=>*
     ([:: vn 3; vn 4], fact_loop).
Proof.
  do 10!stepstep.
  done.
Qed.

(* 任意の自然数についての階乗の計算 *)
Goal forall l m n,
    n = m * l`! ->
    ([:: vn l; vn m], fact_loop) |=>* ([:: vn 0; vn n], [::]).
Proof.
  elim=> // [m n H | l IHl m n H].
  - do !stepstep.
      by rewrite H fact0 muln1.
  - case: l IHl H => [IHl H | l IHl H].
    + do !stepstep.
      rewrite subn1 succnK mul1n H.
        by rewrite factS fact0 2!muln1.
    + do 10!stepstep.
      rewrite /= -/fact_loop.
      apply: IHl.                     (* apply: (IHl (l.+2 * m) n). *)
      rewrite H factS.
      ring.                     (* by rewrite mulnA [m * l.+2]mulnC *)
Qed.

(* END *)
