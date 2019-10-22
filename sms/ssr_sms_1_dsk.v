(** Tezos' Michelson small-setp semantics *)
(** Dual Stack Machine *)
(** @suharahiromicihi *)
(** 2019_10_13 *)

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
| iif (cs1 cs2 : seq inst)                  (* skip なら nil *)
| iloop (cs : seq inst)
| idip (cs : seq inst)
| iadd
| isub
| imul
| ieq
| ineq
| iup                                       (* for idip, internal use *)
| idown                                     (* for idip, internal use *)
.

Definition cstack := seq inst.              (* c :: cs *)
Definition vstack := seq value.             (* v :: vs *)
Definition ustack := seq value.             (* u :: us , auxiliary stack or upper stack *)
Definition env := (ustack * vstack * cstack)%type.   (* e *)

Inductive step : relation env :=            (* env -> env -> Prop *)
| stepseq us vs cs1 cs2 cs : cs1 ++ cs2 = cs ->
                           step (us, vs, iseq cs1 :: cs2)         (us, vs, cs)
| stepdrop us v vs cs :    step (us, v :: vs, idrop :: cs)        (us, vs, cs)
| stepdup us v vs cs :     step (us, v :: vs, idup :: cs)         (us, v :: v :: vs, cs)
| stepswap us v1 v2 vs cs :
                           step (us, v2 :: v1 :: vs, iswap :: cs) (us, v1 :: v2 :: vs, cs)
| steppush_n us n vs cs:   step (us, vs, ipush tn (vn n) :: cs)   (us, (vn n) :: vs, cs)
| steppush_b us b vs cs:   step (us, vs, ipush tb (vb b) :: cs)   (us, (vb b) :: vs, cs)
| stepif_tt us vs cs1 cs2 cs3 cs : cs1 ++ cs3 = cs ->
                           step (us, vb true :: vs, iif cs1 cs2 :: cs3) (us, vs, cs)
| stepif_ff us vs cs1 cs2 cs3 cs : cs2 ++ cs3 = cs ->
                           step (us, vb false :: vs, iif cs1 cs2 :: cs3) (us, vs, cs)
| steploop_tt us vs cs1 cs2 cs : cs1 ++ (iloop cs1 :: cs2) = cs ->
                           step (us, vb true :: vs, iloop cs1 :: cs2) (us, vs, cs)
| steploop_ff us vs cs1 cs2 :
                           step (us, vb false :: vs, iloop cs1 :: cs2) (us, vs, cs2)
| stepdip us vs cs1 cs2 cs : (iup :: cs1) ++ (idown :: cs2) = cs ->
                           step (us, vs, idip cs1 :: cs2) (us, vs, cs)
| stepadd us n1 n2 n3 vs cs : n2 + n1 = n3 ->
                        step (us, [::vn n2, vn n1 & vs], iadd :: cs) (us, vn n3 :: vs, cs)
| stepsub us n1 n2 n3 vs cs : n2 - n1 = n3 ->
                        step (us, [::vn n2, vn n1 & vs], isub :: cs) (us, vn n3 :: vs, cs)
| stepmul us n1 n2 n3 vs cs : n2 * n1 = n3 ->
                        step (us, [::vn n2, vn n1 & vs], imul :: cs) (us, vn n3 :: vs, cs)
| stepeq_tt us vs cs :     step (us, vn 0 :: vs, ieq :: cs)     (us, vb true :: vs, cs)
| stepeq_ff us n vs cs :   step (us, vn n.+1 :: vs, ieq :: cs)  (us, vb false :: vs, cs)
| stepneq_tt us n vs cs :  step (us, vn n.+1 :: vs, ineq :: cs) (us, vb true :: vs, cs)
| stepneq_ff us vs cs :    step (us, vn 0 :: vs, ineq :: cs)    (us, vb false :: vs, cs)
| stepup us v vs cs :      step (us, v :: vs, iup :: cs)        (v :: us, vs, cs)
| stepdown u us vs cs :    step (u :: us, vs, idown :: cs)      (us, u :: vs, cs)
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


(* ********************************* *)
(* step が決定的であることを証明する。 *)
(* ********************************* *)

Ltac i_none := right; inv=> ?; inv; done. (* inst の定義にあわない場合。 *)
Ltac i_done := left; eexists; constructor; done. (* inst の定義にあう場合。 *)

(* 常識的な答え *)
Theorem decide_step (e1 : env) : decidable (exists (e2 : env), e1 |=> e2).
Proof.
  case: e1 => [[us vs] [| c cs]]; try i_none.
  case: c.                                 (* inst で場合分けする。 *)
  - move: cs => cs2 cs1; i_done.           (* seq *)
  - case: vs => [| v vs]; try i_none; i_done.         (* drop *)
  - case: vs => [| v vs]; try i_none; i_done.         (* dup *)
  - case: vs => [| v1 [| v2 vs]]; try i_none; i_done. (* swap *)
  - case=> [] [] n; try i_none; i_done.               (* push *)
  - case: vs => [| [n | b] vs]; try i_none.
    case: b; i_done.                        (* if_tt と if_ff *)
  - case: vs => [| [n | b] vs]; try i_none.
    case: b; i_done.                        (* loop_tt と loop_ff *)
  - move: cs => cs2 cs1; i_done.            (* dip *)
  - case: vs => [| [n1 | b1] [| [n2 | b2] vs]]; try i_none; i_done. (* add *)
  - case: vs => [| [n1 | b1] [| [n2 | b2] vs]]; try i_none; i_done. (* sub *)
  - case: vs => [| [n1 | b1] [| [n2 | b2] vs]]; try i_none; i_done. (* mul *)
  - case: vs => [| [n | b] vs]; try i_none.
    case: n; i_done.                                (* eq_tt と eq_ff *)
  - case: vs => [| [n | b] vs]; try i_none.
    case: n; i_done.                                (* neq_ff と neq_tt *)
  - case: vs => [| v vs]; try i_none; i_done.       (* 追加 up *)
  - case: us => [| u us]; try i_none; i_done.       (* 追加 down *)
Defined.


(* 省略の全く無い答え *)
Theorem decide_step' (e1 : env) : decidable (exists (e2 : env), e1 |=> e2).
Proof.
  case: e1 => [[us vs] cs].
  case: cs => [| c cs]; first i_none.
  case: c.                                 (* inst で場合分けする。 *)
  (* seq *)
  - move: cs => cs2 cs1.
    left.
    exists (us, vs, cs1 ++ cs2).
      by apply: stepseq.
  (* drop *)
  - case: vs => [| v vs]; first i_none.
    left.
    exists (us, vs, cs).
      by apply: stepdrop.
  (* dup *)
  - case: vs => [| v vs]; first i_none.
    left.
    exists (us, [:: v, v & vs], cs).
      by apply: stepdup.
  (* swap *)
  - case: vs => [| v1 vs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    left.
    exists (us, [:: v2, v1 & vs], cs).
      by apply: stepswap.
  (* push *)
  - move=> ty v.
    case: ty; case: v; try i_none.  (* nat か bool で場合分けする。 *)
    (* nat の組み合わせ と bool の組み合わせ以外を try i_none で片付ける。 *)
    + move=> n.
      left.
      exists (us, [:: vn n & vs], cs).
        by apply: steppush_n.
    + move=> b.
      left.
      exists (us, [:: vb b & vs], cs).
        by apply: steppush_b.
  (* if *)
  - case: vs => [| v vs]; first i_none.
    move: cs => cs3 cs1 cs2.
    case: v => [n | b]; first i_none. (* nat か bool で場合分けする。 *)
    case: b.                      (* true か false で場合分けする。 *)
    + left.
      exists (us, vs, cs1 ++ cs3).
        by apply: stepif_tt.
    + left.
      exists (us, vs, cs2 ++ cs3).
        by apply: stepif_ff.
  (* loop *)
  - case: vs => [| v vs]; first i_none.
    move: cs => cs2 cs1.
    case: v => [n | b]; first i_none. (* nat か bool で場合分けする。 *)
    case: b.                      (* true か false で場合分けする。 *)
    + left.
      exists (us, vs, cs1 ++ (iloop cs1 :: cs2)).
        by apply: steploop_tt.
    + left.
      exists (us, vs, cs2).
        by apply: steploop_ff.
        
  (* dip *)
    move: cs => cs2 cs1.
    left.
    exists (us, vs, (iup :: cs1) ++ (idown :: cs2)). (* 補助スタックを使う例。 *)
        by apply: stepdip.
        
  (* add *)
  - case: vs => [| v1 vs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    case: v1; case: v2 => n1 n2; try i_none. (* nat か bool で場合分けする。 *)
    (* nat と nat の組み合わせ以外を try i_none で片付ける。 *)
    left.
    exists (us, vn (n2 + n1) :: vs, cs).
      by apply: stepadd.
  (* sub *)
  - case: vs => [| v1 vs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    case: v1; case: v2 => n1 n2; try i_none.
    left.
    exists (us, vn (n2 - n1) :: vs, cs).
      by apply: stepsub.
  (* mul *)
  - case: vs => [| v1 vs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    case: v1; case: v2 => n1 n2; try i_none.
    left.
    exists (us, vn (n2 * n1) :: vs, cs).
      by apply: stepmul.
  (* eq *)
  - case: vs => [| v vs]; first i_none.
    case: v => n; try i_none.       (* nat か bool で場合分けする。 *)
    case: n.                        (* 0 か 非0 で場合分けする。 *)
    + left.
      exists (us, [:: vb true & vs], cs).
        by apply: stepeq_tt.
    + left.
      exists (us, [:: vb false & vs], cs).
        by apply: stepeq_ff.
  (* neq *)
  - case: vs => [| v vs]; first i_none.
    case: v => n; try i_none.
    case: n.
    + left.
      exists (us, [:: vb false & vs], cs).
        by apply: stepneq_ff.
    + left.
      exists (us, [:: vb true & vs], cs).
        by apply: stepneq_tt.
        
  (* 追加 up *)
  - case: vs => [| v vs]; first i_none.
    left.
    exists ([:: v & us], vs, cs).
      by apply: stepup.
  (* 追加 down *)
  - case: us => [| u us]; first i_none.
    left.
    exists (us, [:: u & vs], cs).
      by apply: stepdown.
Defined.


(* case 文をまとめた例 *)
Theorem decide_step'' (e1 : env) : decidable (exists (e2 : env), e1 |=> e2).
Proof.
  case: e1 => [[us vs] [| c cs]]; first i_none.
  case: c.                                 (* inst で場合分けする。 *)
  (* seq *)
  - move: cs => cs2 cs1.
    left.
    exists (us, vs, cs1 ++ cs2).                (* eexists *)
      by apply: stepseq.                    (* constructor *)
  (* drop *)
  - case: vs => [| v vs]; first i_none.
    left.
    exists (us, vs, cs).
      by apply: stepdrop.
  (* dup *)
  - case: vs => [| v vs]; first i_none.
    left.
    exists (us, [:: v, v & vs], cs).
      by apply: stepdup.
  (* swap *)
  - case: vs => [| v1 [| v2 vs]]; try i_none.
    left.
    exists (us, [:: v2, v1 & vs], cs).
      by apply: stepswap.
  (* push *)
  - move=> ty v.
    case: ty; case: v; try i_none.  (* nat か bool で場合分けする。 *)
    (* nat の組み合わせ と bool の組み合わせ以外を try i_none で片付ける。 *)
    + move=> n.
      left.
      exists (us, [:: vn n & vs], cs).
        by apply: steppush_n.
    + move=> b.
      left.
      exists (us, [:: vb b & vs], cs).
        by apply: steppush_b.
  (* if *)
  - case: vs => [| [n | b] vs]; try i_none.
    move: cs => cs3 cs1 cs2.
    case: b.                      (* true か false で場合分けする。 *)
    + left.
      exists (us, vs, cs1 ++ cs3).
        by apply: stepif_tt.
    + left.
      exists (us, vs, cs2 ++ cs3).
        by apply: stepif_ff.
  (* loop *)
  - case: vs => [| [n | b] vs]; try i_none.
    move: cs => cs2 cs1.
    (* nat か bool で場合分けする。 *)
    case: b.                      (* true か false で場合分けする。 *)
    + left.
      exists (us, vs, cs1 ++ (iloop cs1 :: cs2)).
        by apply: steploop_tt.
    + left.
      exists (us, vs, cs2).
        by apply: steploop_ff.
        
  (* dip *)
  - move: cs => cs2 cs1.
    left.
    exists (us, vs, (iup :: cs1) ++ (idown :: cs2)). (* 補助スタックを使う例。 *)
        by apply: stepdip.
        
  (* add *)
  - case: vs => [| v1 [| v2 vs]]; try i_none.
    case: v1; case: v2 => n1 n2; try i_none. (* nat か bool で場合分けする。 *)
    (* nat と nat の組み合わせ以外を try i_none で片付ける。 *)
    left.
    exists (us, vn (n2 + n1) :: vs, cs).
      by apply: stepadd.
  (* sub *)
  - case: vs => [| v1 [| v2 vs]]; try i_none.
    case: v1; case: v2 => n1 n2; try i_none.
    left.
    exists (us, vn (n2 - n1) :: vs, cs).
      by apply: stepsub.
  (* mul *)
  - case: vs => [| v1 [| v2 vs]]; try i_none.
    case: v1; case: v2 => n1 n2; try i_none.
    left.
    exists (us, vn (n2 * n1) :: vs, cs).
      by apply: stepmul.
  (* eq *)
  - case: vs => [| v vs]; first i_none.
    case: v => n; try i_none.       (* nat か bool で場合分けする。 *)
    case: n.                        (* 0 か 非0 で場合分けする。 *)
    + left.
      exists (us, [:: vb true & vs], cs).
        by apply: stepeq_tt.
    + left.
      exists (us, [:: vb false & vs], cs).
        by apply: stepeq_ff.
  (* neq *)
  - case: vs => [| v vs]; first i_none.
    case: v => n; try i_none.
    case: n.
    + left.
      exists (us, [:: vb false & vs], cs).
        by apply: stepneq_ff.
    + left.
      exists (us, [:: vb true & vs], cs).
        by apply: stepneq_tt.
        
  (* 追加 up *)
  - case: vs => [| v vs]; first i_none.
    left.
    exists ([:: v & us], vs, cs).
      by apply: stepup.
  (* 追加 down *)
  - case: us => [| u us]; first i_none.
    left.
    exists (us, [:: u & vs], cs).
      by apply: stepdown.
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

(* ********************************** *)
(* スタックの後ろにリストを付け加える。 *)
(* ********************************** *)
Theorem step_apptail (us1 us2 us3 : ustack)
        (vs1 vs2 vs3 : vstack) (cs1 cs2 cs3 : cstack) :
  (us1, vs1, cs1) |=> (us2, vs2, cs2) ->
  (us1 ++ us3, vs1 ++ vs3, cs1 ++ cs3) |=> (us2 ++ us3, vs2 ++ vs3, cs2 ++ cs3).
Proof.
  by inv=> //=; try rewrite -catA; constructor.
Qed.
(* constructor は、stepseq など。 *)

Theorem steprsc_apptail (us1 us2 us3 : ustack)
        (vs1 vs2 vs3 : vstack) (cs1 cs2 cs3 : cstack) :
  (us1, vs1, cs1) |=>* (us2, vs2, cs2) ->
  (us1 ++ us3, vs1 ++ vs3, cs1 ++ cs3) |=>* (us2 ++ us3, vs2 ++ vs3, cs2 ++ cs3).
Proof.
  move=> H.
  apply: steprsc_trans.
  -  admit.
  - apply: steprsc_step.
    + apply: step_apptail => //.
      admit.
    + done.
Admitted.


(***********************)
(* 自動証明 ************)
(***********************)
Lemma exists_and_right_map (P Q R : inst -> Prop) :
  (forall i, Q i -> R i) -> (exists i, P i /\ Q i) -> (exists i, P i /\ R i).
Proof.
(*
  move=> HQR [i [HP HQ]].
  exists i.
  split.
  - done.
  - by apply: HQR.
  Restart.
*)
    by firstorder.
Qed.

Ltac stepstep_0 e1 e2 :=
  apply: steprsc_refl ||
  match eval hnf in (decide_step e1) with
  | left (ex_intro _ _ ?p) => apply: (steprsc_step p)
  end.

Ltac stepstep_1 e1 e2 :=
  (eexists; split; last apply: steprsc_refl) ||
  match eval hnf in (decide_step e1) with
  | left (ex_intro _ _ ?p) =>
    apply: (exists_and_right_map (fun _ => steprsc_step p))
  end.

Ltac stepstep_2 e1 e2 :=
  (eexists; split; last (eexists; split; last apply: steprsc_refl)) ||
  match eval hnf in (decide_step e1) with
  | left (ex_intro _ _ ?p) =>
    apply: (exists_and_right_map (fun _ =>
            exists_and_right_map (fun _ => steprsc_step p)))
  end.

Ltac stepstep :=
  match goal with
  | |- ?e1 |=>* ?e2 => stepstep_0 e1 e2
  | |- (exists i1, _ /\ ?e1 |=>* ?e2) => stepstep_1 e1 e2
  | |- (exists i1, _ /\ (exists i2, _ /\ ?e1 |=>* ?e2)) => stepstep_2 e1 e2
  end.

Ltac stepstep_trace :=
  match goal with
  | |- ?e1 |=>* ?e2 => stepstep_0 e1 e2; idtac e1
  | |- (exists i1, _ /\ ?e1 |=>* ?e2) => stepstep_1 e1 e2; idtac e1
  | |- (exists i1, _ /\ (exists i2, _ /\ ?e1 |=>* ?e2)) => stepstep_2 e1 e2; idtac e1
  end.

Ltac stepauto := repeat stepstep.
Ltac stepauto_trace := repeat stepstep_trace.


(***********************)
(* 手動証明 ************)
(***********************)
(*
Tactic Notation "steppartial" constr(H) "by" tactic(tac) :=
  (eapply steprsc_trans 
   [by eapply H; tac |]) ||
  (refine (exists_and_right_map (fun _ => steprsc_trans _) _);
   [by eapply H; tac |]) ||
  (refine (exists_and_right_map (fun _ =>
           exists_and_right_map (fun _ => steprsc_trans _)) _);
   [by eapply H; tac |]).
 *)

Tactic Notation "steppartial" constr(H) "by" tactic(tac) :=
  eapply steprsc_trans;
  [by (apply steprsc_step'; eapply H) || eapply H; tac |].
(*   subst_evars. *)
                                               
Tactic Notation "steppartial" constr(H) := steppartial H by idtac.

Ltac rscrefl := apply steprsc_refl' ; repeat f_equal.
  

(* sample *)

Definition inop := [:: ipush tn 42; idrop].

Lemma stepnop us vs cs :
  (us, vs, [:: ipush tn 42, idrop & cs]) |=>* (us, vs, cs).
Proof.
  Check decide_step (us, vs, [:: ipush tn 42, idrop & cs]).
  Eval hnf in (decide_step (us, vs, [:: ipush tn 42, idrop & cs])).
  Check steprsc_step (steppush_n us 42 vs (idrop :: cs)).
  apply: (steprsc_step (steppush_n us 42 vs (idrop :: cs))).
  Check stepdrop us 42 vs cs.
  apply: (steprsc_step (stepdrop us 42 vs cs)).
    by apply: steprsc_refl.
  
  Restart.
  stepstep_0 (us, vs, [:: ipush tn 42, idrop & cs]) (us, vs, cs).
  stepstep_0 (us, [:: vn 42 & vs], [:: idrop & cs]) (us, vs, cs).
    by apply: steprsc_refl.

  Restart.
    by stepauto.
Qed.


(* ********** *)
(* 階乗の計算 *)
(* ********** *)
Definition sample0 :=
  [::
     ipush tn 1;
     ipush tn 2;
     iadd;
     idrop;
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
     idrop;
     idrop
  ].

Goal ([::], [::], fact) |=>* ([::], [::], [::]).
Proof.
    by stepauto.
Qed.


Definition fact_loop_body :=
  [::
     idup;
     idip [:: imul];
     ipush tn 1;
     iswap;
     isub;
     idup;
     ineq
  ].

Definition fact_loop :=
  [::
     ineq;
     iloop fact_loop_body
  ].

Definition fact' :=
  [::
     ipush tn 1;
     iswap;
     idup;
     iseq fact_loop;
     idrop
  ].

Goal ([::], [:: vn 4; vn 1], fact_loop_body) |=>*
     ([::], [:: vb true; vn 3; vn 4], [::]).
Proof.
    by stepauto.
Qed.

Goal ([::], [:: vn 4; vn 4; vn 1], fact_loop) |=>*
     ([::], [:: vn 0; vn 24], [::]).
Proof.
    by stepauto.
Qed.

Goal ([::], [:: vn 4], fact') |=>* ([::], [:: vn 24], [::]).
Proof.
    by stepauto.
Qed.

(* 任意の自然数についての階乗の計算 *)
Goal forall l m n,
    n = m * l`! ->
    ([::], [:: vn l; vn l; vn m], fact_loop) |=>* ([::], [:: vn 0; vn n], [::]).
Proof.
  elim=> // [m n H | l IHl m n H].
  - stepauto.
      by rewrite H fact0 muln1.
  - stepauto.
    rewrite subn1 PeanoNat.Nat.pred_succ /=.
    case: l IHl H => [IHl H | l IHl H].
    + stepauto.                             (* l = 0 *)
        by rewrite H mul1n factS fact0 2!muln1.
    + apply: (IHl (l.+2 * m) n).            (* l = l.+1 *)
      rewrite H factS.
      ring.                    (* by rewrite mulnA [m * l.+2]mulnC *)
Qed.

(*
Goal ([::], [::], fact) |=>* ([::], [::], [::]).
Proof.
  rewrite /fact.
  apply rsc_step with
      (y:=([::], [:: vn 1],
           [:: ipush tn 4; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: steppush_n.
  apply rsc_step with
      (y:=([::], [:: vn 4; vn 1],
           [:: idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: steppush_n.
  apply rsc_step with
      (y:=([::], [:: vn 4; vn 4; vn 1],
           [:: ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdup.
  apply rsc_step with
      (y:=([::], [:: vb true; vn 4; vn 1],
           [:: iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepneq_tt.
  (* **** *)
  apply rsc_step with
      (y:=([::], [:: vn 4; vn 1],
           [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: steploop_tt.
  apply rsc_step with
      (y:=([::], [:: vn 4; vn 4; vn 1],
           [:: idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdup.
  apply rsc_step with
      (y:=([::], [:: vn 4; vn 4; vn 1],
           [:: iup; imul; idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdip.
  apply rsc_step with
      (y:=([:: vn 4], [:: vn 4; vn 1],
           [:: imul; idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepup.
  apply rsc_step with
      (y:=([:: vn 4], [:: vn 4],
           [:: idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepmul.
  apply rsc_step with
      (y:=([::], [:: vn 4; vn 4],
           [:: ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdown.
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 4; vn 4],
           [:: iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: steppush_n.
  apply rsc_step with
      (y:=([::], [:: vn 4; vn 1; vn 4],
           [:: isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepswap.
  apply rsc_step with
      (y:=([::], [:: vn 3; vn 4],
           [:: idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepsub.
  apply rsc_step with
      (y:=([::], [:: vn 3; vn 3; vn 4],
           [:: ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdup.
  apply rsc_step with
      (y:=([::], [:: vb true; vn 3; vn 4],
           [:: iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepneq_tt.
  (* **** *)
  apply rsc_step with
      (y:=([::], [:: vn 3; vn 4],
           [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: steploop_tt.
  apply rsc_step with
      (y:=([::], [:: vn 3; vn 3; vn 4],
           [:: idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdup.
  apply rsc_step with
      (y:=([::], [:: vn 3; vn 3; vn 4],
           [:: iup; imul; idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdip.
  apply rsc_step with
      (y:=([:: vn 3], [:: vn 3; vn 4],
           [:: imul; idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepup.
  apply rsc_step with
      (y:=([:: vn 3], [:: vn 12],
           [:: idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepmul.
  apply rsc_step with
      (y:=([::], [:: vn 3; vn 12],
           [:: ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdown.
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 3; vn 12],
           [:: iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: steppush_n.
  apply rsc_step with
      (y:=([::], [:: vn 3; vn 1; vn 12],
           [:: isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepswap.
  apply rsc_step with
      (y:=([::], [:: vn 2; vn 12],
           [:: idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepsub.
  apply rsc_step with
      (y:=([::], [:: vn 2; vn 2; vn 12],
           [:: ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdup.
  apply rsc_step with
      (y:=([::], [:: vb true; vn 2; vn 12],
           [:: iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepneq_tt.
  apply rsc_step with
      (y:=([::], [:: vn 2; vn 12],
           [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: steploop_tt.
  (* **** *)
  apply rsc_step with
      (y:=([::], [:: vn 2; vn 2; vn 12],
           [:: idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdup.
  apply rsc_step with
      (y:=([::], [:: vn 2; vn 2; vn 12],
           [:: iup; imul; idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdip.
  apply rsc_step with
      (y:=([:: vn 2], [:: vn 2; vn 12],
           [:: imul; idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepup.
  apply rsc_step with
      (y:=([:: vn 2], [:: vn 24],
           [:: idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepmul.
  apply rsc_step with
      (y:=([::], [:: vn 2; vn 24],
           [:: ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdown.
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 2; vn 24],
           [:: iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: steppush_n.
  apply rsc_step with
      (y:=([::], [:: vn 2; vn 1; vn 24],
           [:: isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepswap.
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 24],
           [:: idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepsub.
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 1; vn 24],
           [:: ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdup.
  apply rsc_step with
      (y:=([::], [:: vb true; vn 1; vn 24],
           [:: iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepneq_tt.
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 24],
           [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: steploop_tt.
  (* **** *)
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 1; vn 24],
           [:: idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdup.
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 1; vn 24],
           [:: iup; imul; idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdip.
  apply rsc_step with
      (y:=([:: vn 1], [:: vn 1; vn 24],
           [:: imul; idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepup.
  apply rsc_step with
      (y:=([:: vn 1], [:: vn 24],
           [:: idown; ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepmul.
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 24],
           [:: ipush tn 1; iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdown.
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 1; vn 24],
           [:: iswap; isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: steppush_n.
  apply rsc_step with
      (y:=([::], [:: vn 1; vn 1; vn 24],
           [:: isub; idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepswap.
  apply rsc_step with
      (y:=([::], [:: vn 0; vn 24],
           [:: idup; ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepsub.
  apply rsc_step with
      (y:=([::], [:: vn 0; vn 0; vn 24],
           [:: ineq;
            iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepdup.
  apply rsc_step with
      (y:=([::], [:: vb false; vn 0; vn 24],
           [:: iloop [:: idup; idip [:: imul]; ipush tn 1; iswap; isub; idup; ineq];
            idrop; idrop]));
    first by apply: stepneq_ff.
  apply rsc_step with
      (y:=([::], [:: vn 0; vn 24],
           [:: idrop; idrop]));
    first by apply: steploop_ff.
  (* **** *)  
  apply rsc_step with
      (y:=([::], [:: vn 24],
           [:: idrop]));
    first by apply: stepdrop.
  apply rsc_step with
      (y:=([::], [::],
           [::]));
    first by apply: stepdrop.

  by apply rsc_refl.
Qed.

Goal ([::], [::], fact) |=>* ([::], [::], [::]).
Proof.
  rewrite /fact.
  eapply rsc_step with (y:=([::], [:: vn 1], _));
    first by apply: steppush_n.
  eapply rsc_step with (y:=([::], [:: vn 4; vn 1], _));
    first by apply: steppush_n.
  eapply rsc_step with (y:=([::], [:: vn 4; vn 4; vn 1], _));
    first by apply: stepdup.
  eapply rsc_step with (y:=([::], [:: vb true; vn 4; vn 1], _));
    first by apply: stepneq_tt.
  (* **** *)
  eapply rsc_step with (y:=([::], [:: vn 4; vn 1], _));
    first by apply: steploop_tt.
  eapply rsc_step with (y:=([::], [:: vn 4; vn 4; vn 1], _));
    first by apply: stepdup.
  eapply rsc_step with (y:=([::], [:: vn 4; vn 4; vn 1], _));
    first by apply: stepdip.
  eapply rsc_step with (y:=([:: vn 4], [:: vn 4; vn 1], _));
    first by apply: stepup.
  eapply rsc_step with (y:=([:: vn 4], [:: vn 4], _));
    first by apply: stepmul.
  eapply rsc_step with (y:=([::], [:: vn 4; vn 4], _));
    first by apply: stepdown.
  eapply rsc_step with (y:=([::], [:: vn 1; vn 4; vn 4], _));
    first by apply: steppush_n.
  eapply rsc_step with (y:=([::], [:: vn 4; vn 1; vn 4], _));
    first by apply: stepswap.
  eapply rsc_step with (y:=([::], [:: vn 3; vn 4], _));
    first by apply: stepsub.
  eapply rsc_step with (y:=([::], [:: vn 3; vn 3; vn 4], _));
    first by apply: stepdup.
  eapply rsc_step with (y:=([::], [:: vb true; vn 3; vn 4], _));
    first by apply: stepneq_tt.
  (* **** *)
  eapply rsc_step with (y:=([::], [:: vn 3; vn 4], _));
    first by apply: steploop_tt.
  eapply rsc_step with (y:=([::], [:: vn 3; vn 3; vn 4], _));
    first by apply: stepdup.
  eapply rsc_step with (y:=([::], [:: vn 3; vn 3; vn 4], _));
    first by apply: stepdip.
  eapply rsc_step with (y:=([:: vn 3], [:: vn 3; vn 4], _));
    first by apply: stepup.
  eapply rsc_step with (y:=([:: vn 3], [:: vn 12], _));
    first by apply: stepmul.
  eapply rsc_step with (y:=([::], [:: vn 3; vn 12], _));
    first by apply: stepdown.
  eapply rsc_step with (y:=([::], [:: vn 1; vn 3; vn 12], _));
    first by apply: steppush_n.
  eapply rsc_step with (y:=([::], [:: vn 3; vn 1; vn 12], _));
    first by apply: stepswap.
  eapply rsc_step with (y:=([::], [:: vn 2; vn 12], _));
    first by apply: stepsub.
  eapply rsc_step with (y:=([::], [:: vn 2; vn 2; vn 12], _));
    first by apply: stepdup.
  eapply rsc_step with (y:=([::], [:: vb true; vn 2; vn 12], _));
    first by apply: stepneq_tt.
  eapply rsc_step with (y:=([::], [:: vn 2; vn 12], _));
    first by apply: steploop_tt.
  (* **** *)
  eapply rsc_step with (y:=([::], [:: vn 2; vn 2; vn 12], _));
    first by apply: stepdup.
  eapply rsc_step with (y:=([::], [:: vn 2; vn 2; vn 12], _));
    first by apply: stepdip.
  eapply rsc_step with (y:=([:: vn 2], [:: vn 2; vn 12], _));
    first by apply: stepup.
  eapply rsc_step with (y:=([:: vn 2], [:: vn 24], _));
    first by apply: stepmul.
  eapply rsc_step with (y:=([::], [:: vn 2; vn 24], _));
    first by apply: stepdown.
  eapply rsc_step with (y:=([::], [:: vn 1; vn 2; vn 24], _));
    first by apply: steppush_n.
  eapply rsc_step with (y:=([::], [:: vn 2; vn 1; vn 24], _));
    first by apply: stepswap.
  eapply rsc_step with (y:=([::], [:: vn 1; vn 24], _));
    first by apply: stepsub.
  eapply rsc_step with (y:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepdup.
  eapply rsc_step with (y:=([::], [:: vb true; vn 1; vn 24], _));
    first by apply: stepneq_tt.
  eapply rsc_step with (y:=([::], [:: vn 1; vn 24], _));
    first by apply: steploop_tt.
  (* **** *)
  eapply rsc_step with (y:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepdup.
  eapply rsc_step with (y:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepdip.
  eapply rsc_step with (y:=([:: vn 1], [:: vn 1; vn 24], _));
    first by apply: stepup.
  eapply rsc_step with (y:=([:: vn 1], [:: vn 24], _));
    first by apply: stepmul.
  eapply rsc_step with (y:=([::], [:: vn 1; vn 24], _));
    first by apply: stepdown.
  eapply rsc_step with (y:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: steppush_n.
  eapply rsc_step with (y:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepswap.
  eapply rsc_step with (y:=([::], [:: vn 0; vn 24], _));
    first by apply: stepsub.
  eapply rsc_step with (y:=([::], [:: vn 0; vn 0; vn 24], _));
    first by apply: stepdup.
  eapply rsc_step with (y:=([::], [:: vb false; vn 0; vn 24], _));
    first by apply: stepneq_ff.
  eapply rsc_step with (y:=([::], [:: vn 0; vn 24], _));
    first by apply: steploop_ff.
  (* **** *) 
  eapply rsc_step with (y:=([::], [:: vn 24], _));
    first by apply: stepdrop.
  eapply rsc_step with (y:=([::], [::], _));
    first by apply: stepdrop.
  by eapply rsc_refl.
Qed.

Goal ([::], [::], fact) |=>* ([::], [::], [::]).
Proof.
  rewrite /fact.
  eapply steprsc_step with (e2:=([::], [:: vn 1], _));
    first by apply: steppush_n.
  eapply steprsc_step with (e2:=([::], [:: vn 4; vn 1], _));
    first by apply: steppush_n.
  eapply steprsc_step with (e2:=([::], [:: vn 4; vn 4; vn 1], _));
    first by apply: stepdup.
  eapply steprsc_step with (e2:=([::], [:: vb true; vn 4; vn 1], _));
    first by apply: stepneq_tt.
  (* **** *)
  eapply steprsc_step with (e2:=([::], [:: vn 4; vn 1], _));
    first by apply: steploop_tt.
  eapply steprsc_step with (e2:=([::], [:: vn 4; vn 4; vn 1], _));
    first by apply: stepdup.
  eapply steprsc_step with (e2:=([::], [:: vn 4; vn 4; vn 1], _));
    first by apply: stepdip.
  eapply steprsc_step with (e2:=([:: vn 4], [:: vn 4; vn 1], _));
    first by apply: stepup.
  eapply steprsc_step with (e2:=([:: vn 4], [:: vn 4], _));
    first by apply: stepmul.
  eapply steprsc_step with (e2:=([::], [:: vn 4; vn 4], _));
    first by apply: stepdown.
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 4; vn 4], _));
    first by apply: steppush_n.
  eapply steprsc_step with (e2:=([::], [:: vn 4; vn 1; vn 4], _));
    first by apply: stepswap.
  eapply steprsc_step with (e2:=([::], [:: vn 3; vn 4], _));
    first by apply: stepsub.
  eapply steprsc_step with (e2:=([::], [:: vn 3; vn 3; vn 4], _));
    first by apply: stepdup.
  eapply steprsc_step with (e2:=([::], [:: vb true; vn 3; vn 4], _));
    first by apply: stepneq_tt.
  (* **** *)
  eapply steprsc_step with (e2:=([::], [:: vn 3; vn 4], _));
    first by apply: steploop_tt.
  eapply steprsc_step with (e2:=([::], [:: vn 3; vn 3; vn 4], _));
    first by apply: stepdup.
  eapply steprsc_step with (e2:=([::], [:: vn 3; vn 3; vn 4], _));
    first by apply: stepdip.
  eapply steprsc_step with (e2:=([:: vn 3], [:: vn 3; vn 4], _));
    first by apply: stepup.
  eapply steprsc_step with (e2:=([:: vn 3], [:: vn 12], _));
    first by apply: stepmul.
  eapply steprsc_step with (e2:=([::], [:: vn 3; vn 12], _));
    first by apply: stepdown.
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 3; vn 12], _));
    first by apply: steppush_n.
  eapply steprsc_step with (e2:=([::], [:: vn 3; vn 1; vn 12], _));
    first by apply: stepswap.
  eapply steprsc_step with (e2:=([::], [:: vn 2; vn 12], _));
    first by apply: stepsub.
  eapply steprsc_step with (e2:=([::], [:: vn 2; vn 2; vn 12], _));
    first by apply: stepdup.
  eapply steprsc_step with (e2:=([::], [:: vb true; vn 2; vn 12], _));
    first by apply: stepneq_tt.
  eapply steprsc_step with (e2:=([::], [:: vn 2; vn 12], _));
    first by apply: steploop_tt.
  (* **** *)
  eapply steprsc_step with (e2:=([::], [:: vn 2; vn 2; vn 12], _));
    first by apply: stepdup.
  eapply steprsc_step with (e2:=([::], [:: vn 2; vn 2; vn 12], _));
    first by apply: stepdip.
  eapply steprsc_step with (e2:=([:: vn 2], [:: vn 2; vn 12], _));
    first by apply: stepup.
  eapply steprsc_step with (e2:=([:: vn 2], [:: vn 24], _));
    first by apply: stepmul.
  eapply steprsc_step with (e2:=([::], [:: vn 2; vn 24], _));
    first by apply: stepdown.
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 2; vn 24], _));
    first by apply: steppush_n.
  eapply steprsc_step with (e2:=([::], [:: vn 2; vn 1; vn 24], _));
    first by apply: stepswap.
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 24], _));
    first by apply: stepsub.
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepdup.
  eapply steprsc_step with (e2:=([::], [:: vb true; vn 1; vn 24], _));
    first by apply: stepneq_tt.
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 24], _));
    first by apply: steploop_tt.
  (* **** *)
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepdup.
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepdip.
  eapply steprsc_step with (e2:=([:: vn 1], [:: vn 1; vn 24], _));
    first by apply: stepup.
  eapply steprsc_step with (e2:=([:: vn 1], [:: vn 24], _));
    first by apply: stepmul.
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 24], _));
    first by apply: stepdown.
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: steppush_n.
  eapply steprsc_step with (e2:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepswap.
  eapply steprsc_step with (e2:=([::], [:: vn 0; vn 24], _));
    first by apply: stepsub.
  eapply steprsc_step with (e2:=([::], [:: vn 0; vn 0; vn 24], _));
    first by apply: stepdup.
  eapply steprsc_step with (e2:=([::], [:: vb false; vn 0; vn 24], _));
    first by apply: stepneq_ff.
  eapply steprsc_step with (e2:=([::], [:: vn 0; vn 24], _));
    first by apply: steploop_ff.
  (* **** *) 
  eapply steprsc_step with (e2:=([::], [:: vn 24], _));
    first by apply: stepdrop.
  eapply steprsc_step with (e2:=([::], [::], _));
    first by apply: stepdrop.
  by eapply steprsc_refl.
Qed.
*)

(** example 1 *)

Definition example1 :=
  [::                                        (* a b c d *)
     idip [:: idrop; idup; idip [:: iswap]]; (* a c d c *)
     iswap; idip [:: iswap];                 (* c d a c *)
       iswap                                 (* d c a c *)
  ].

Definition example2 :=
  [::                                            (* a b c d *)
     iup; idrop; idup; iup; iswap; idown; idown; (* a c d c *)
     iswap; iup; iswap; idown;                   (* c d a c *)
       iswap                                     (* d c a c *)
  ].

Lemma stepexample1 (a b c d : value) :
  ([::], [:: a; b; c; d], example1) |=>* ([::], [:: d; c; a; c], [::]).
Proof.
    by stepauto.
Qed.

Lemma stepexample2 (a b c d : value) :
  ([::], [:: a; b; c; d], example2) |=>* ([::], [:: d; c; a; c], [::]).
Proof.
    by stepauto.
Qed.

Lemma stepexample2' (a b c d : value) :
  {p | ([::], [:: a; b; c; d], p) |=>* ([::], [:: d; c; a; c], [::])}.
Proof.
  eexists.
  eapply steprsc_step; first apply stepup.
  eapply steprsc_step; first apply stepdrop.
  eapply steprsc_step; first apply stepdup.
  eapply steprsc_step; first apply stepup.
  eapply steprsc_step; first apply stepswap.
  eapply steprsc_step; first apply stepdown.
  eapply steprsc_step; first apply stepdown.
  eapply steprsc_step; first apply stepswap.
  eapply steprsc_step; first apply stepup.
  eapply steprsc_step; first apply stepswap.
  eapply steprsc_step; first apply stepdown.
  eapply steprsc_step; first apply stepswap.
  done.
Defined.

Lemma stepexample12'' (a b c d : value) :
  {p | ([::], [:: a; b; c; d], p) |=>* ([::], [:: d; c; a; c], [::])}.
Proof.
  eexists.
  steppartial stepup.
  steppartial stepdrop.
  steppartial stepdup.
  steppartial stepup.
  steppartial stepswap.
  steppartial stepdown.
  steppartial stepdown.
  steppartial stepswap.
  steppartial stepup.
  steppartial stepswap.
  steppartial stepdown.
  steppartial stepswap.
  done.
Defined.

(* END *)
