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

Definition sample1 :=
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

Definition fact' :=
  [::
     ipush tn 1;
     ipush tn 4;
     idup;
     ineq;
     iloop [::
              idup;
              iseq [:: iup; imul; idown];
              ipush tn 1;
              iswap;
              isub;
              idup;
              ineq
           ];
     idrop
  ].

Inductive step : relation env :=            (* env -> env -> Prop *)
| stepseq us vs cs1 cs2 cs : cs1 ++ cs2 = cs ->
                           step (us, vs, iseq cs1 :: cs2)         (us, vs, cs)
| stepdrop us v vs cs :    step (us, v :: vs, idrop :: cs)        (us, vs, cs)
| stepdup us v vs cs :     step (us, v :: vs, idup :: cs)         (us, v :: v :: vs, cs)
| stepswap us v1 v2 vs cs :
                           step (us, v2 :: v1 :: vs, iswap :: cs) (us, v1 :: v2 :: vs, cs)
| steppush_n us n vs cs:   step (us, vs, ipush tn (vn n) :: cs)   (us, (vn n) :: vs, cs)
| steppush_b us b vs cs:   step (us, vs, ipush tb (vb b) :: cs)   (us, (vb b) :: vs, cs)
| steploop_tt us vs cs1 cs2 cs : cs1 ++ (iloop cs1 :: cs2) = cs ->
                           step (us, vb true :: vs, iloop cs1 :: cs2) (us, vs, cs)
| steploop_ff us vs cs1 cs2 :
                           step (us, vb false :: vs, iloop cs1 :: cs2) (us, vs, cs2)
| stepdip us v vs1 vs2 cs1 cs2 cs : (iup :: cs1) ++ (idown :: cs2) = cs ->
                        step (us, v :: vs1, idip cs1 :: cs2) (vs2, cs)
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

(* rsc_refl *)
Lemma steprtc_refl (e : env) : e |=>* e.
Proof. done. Qed.

Lemma steprtc_refl' (e1 e2 : env) : e1 = e2 -> e1 |=>* e2.
Proof. by move=> <-. Qed.

Lemma steprtc_step (e1 e2 : env) : e1 |=> e2 -> e1 |=>* e2.
Proof. by do !econstructor. Qed.

(* rsc_step. *)
Lemma steprtc_cons (e1 e2 e3 : env) : e1 |=> e2 -> e2 |=>* e3 -> e1 |=>* e3.
Proof. by econstructor; eauto. Qed.

(* rsc_trans *)
Lemma steprtc_trans (e1 e2 e3 : env) : e1 |=>* e2 -> e2 |=>* e3 -> e1 |=>* e3.
Proof. by apply: rsc_trans. Qed.


(* step が決定的であることを証明する。 *)

Ltac i_none := right; inv=> ?; inv; done. (* inst の定義にあわない場合。 *)
Ltac i_done := left; eexists; constructor; done. (* inst の定義にあう場合。 *)

Theorem decide_step (e1 : env) : decidable (exists (e2 : env), e1 |=> e2).
Proof.
  case: e1 => [[us vs] [| c cs]]; try i_none.
  case: c.                                 (* inst で場合分けする。 *)
  - move: cs => cs1 cs2; i_done.           (* seq *)
  - case: vs => [| v vs]; try i_none; i_done.         (* drop *)
  - case: vs => [| v vs]; try i_none; i_done.         (* dup *)
  - case: vs => [| v1 [| v2 vs]]; try i_none; i_done. (* swap *)
  - case; case=> n; try i_none; i_done.               (* push *)
  - case: vs => [| [n | b] vs]; try i_none.
    case: b; i_done.                        (* loop tt と  ff *)
    
  - case: vs => [|v vs]; first i_none.
    move=> cs2.
    left.
    exists (us, vs, (iup :: cs2) ++ (idown :: cs)).
        by apply: stepdip.                  (* dip *)
        
  - case: vs => [| [n1 | b1] [| [n2 | b2] vs]]; try i_none; i_done. (* add *)
  - case: vs => [| [n1 | b1] [| [n2 | b2] vs]]; try i_none; i_done. (* sub *)
  - case: vs => [| [n1 | b1] [| [n2 | b2] vs]]; try i_none; i_done. (* mul *)
  - case: vs => [| [n | b] vs]; try i_none.
    case: n; i_done.                                (* eq tt と ff *)
  - case: vs => [| [n | b] vs]; try i_none.
    case: n; i_done.                                (* neq ff と tt *)
  - case: vs => [| v vs]; try i_none; i_done. (* 追加 up *)
  - case: us => [| u us]; try i_none; i_done. (* 追加 down *)
Qed.


Theorem decide_step' (e1 : env) : decidable (exists (e2 : env), e1 |=> e2).
Proof.
  case: e1 => [[us vs] cs].
  case: cs => [| c]; first i_none.
  case: c.                                 (* inst で場合分けする。 *)
  (* seq *)
  - move=> cs1 cs2.
    left.
    exists (us, vs, cs1 ++ cs2).
      by apply: stepseq.
  (* drop *)
  - case: vs => [cs | v vs cs]; first i_none.
    left.
    exists (us, vs, cs).
      by apply: stepdrop.
  (* dup *)
  - case: vs => [cs | v vs cs]; first i_none.
    left.
    exists (us, [:: v, v & vs], cs).
      by apply: stepdup.
  (* swap *)
  - case: vs => [cs | v1 vs cs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    left.
    exists (us, [:: v2, v1 & vs], cs).
      by apply: stepswap.
  (* push *)
  - move=> ty v cs.
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
  (* loop *)
  - case: vs => [cs | v vs cs1 cs2]; first i_none.
    case: v => [n | b]; first i_none. (* nat か bool で場合分けする。 *)
    case: b.                      (* true か false で場合分けする。 *)
    + left.
      exists (us, vs, cs1 ++ (iloop cs1 :: cs2)).
        by apply: steploop_tt.
    + left.
      exists (us, vs, cs2).
        by apply: steploop_ff.
        
  (* dip *)
  - case: vs => [cs1 cs2 |v vs cs1 cs2]; first i_none.
    left.
    exists (us, vs, (iup :: cs1) ++ (idown :: cs2)). (* 補助スタックを使う例。 *)
        by apply: stepdip.
        
  (* add *)
  - case: vs => [cs | v1 vs cs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    case: v1; case: v2 => n1 n2; try i_none. (* nat か bool で場合分けする。 *)
    (* nat と nat の組み合わせ以外を try i_none で片付ける。 *)
    left.
    exists (us, vn (n2 + n1) :: vs, cs).
      by apply: stepadd.
  (* sub *)
  - case: vs => [cs | v1 vs cs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    case: v1; case: v2 => n1 n2; try i_none.
    left.
    exists (us, vn (n2 - n1) :: vs, cs).
      by apply: stepsub.
  (* mul *)
  - case: vs => [cs | v1 vs cs]; first i_none.
    case: vs => [| v2 vs]; first i_none.
    case: v1; case: v2 => n1 n2; try i_none.
    left.
    exists (us, vn (n2 * n1) :: vs, cs).
      by apply: stepmul.
  (* eq *)
  - case: vs => [cs | v vs cs]; first i_none.
    case: v => n; try i_none.       (* nat か bool で場合分けする。 *)
    case: n.                        (* 0 か 非0 で場合分けする。 *)
    + left.
      exists (us, [:: vb true & vs], cs).
        by apply: stepeq_tt.
    + left.
      exists (us, [:: vb false & vs], cs).
        by apply: stepeq_ff.
  (* neq *)
  - case: vs => [cs | v vs cs]; first i_none.
    case: v => n; try i_none.
    case: n.
    + left.
      exists (us, [:: vb false & vs], cs).
        by apply: stepneq_ff.
    + left.
      exists (us, [:: vb true & vs], cs).
        by apply: stepneq_tt.
        
  (* 追加 up *)
  - case: vs => [cs | v vs cs]; first i_none.
    left.
    exists ([:: v & us], vs, cs).
      by apply: stepup.
  (* 追加 down *)
  - case: us => [cs | u us cs]; first i_none.
    left.
    exists (us, [:: u & vs], cs).
      by apply: stepdown.
Defined.


Theorem decide_step'' (e1 : env) : decidable (exists (e2 : env), e1 |=> e2).
Proof.
  case: e1 => [[us vs] [| c]]; first i_none.
  case: c.                                 (* inst で場合分けする。 *)
  (* seq *)
  - move=> cs1 cs2.
    left.
    exists (us, vs, cs1 ++ cs2).                (* eexists *)
      by apply: stepseq.                    (* constructor *)
  (* drop *)
  - case: vs => [cs | v vs cs]; first i_none.
    left.
    exists (us, vs, cs).
      by apply: stepdrop.
  (* dup *)
  - case: vs => [cs | v vs cs]; first i_none.
    left.
    exists (us, [:: v, v & vs], cs).
      by apply: stepdup.
  (* swap *)
  - case: vs => [cs | v1 [| v2 vs] cs]; try i_none.
    left.
    exists (us, [:: v2, v1 & vs], cs).
      by apply: stepswap.
  (* push *)
  - move=> ty v cs.
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
  (* loop *)
  - case: vs => [cs | [n | b] vs cs1 cs2]; try i_none.
    (* nat か bool で場合分けする。 *)
    case: b.                      (* true か false で場合分けする。 *)
    + left.
      exists (us, vs, cs1 ++ (iloop cs1 :: cs2)).
        by apply: steploop_tt.
    + left.
      exists (us, vs, cs2).
        by apply: steploop_ff.
        
  (* dip *)
  - case: vs => [cs1 cs2 |v vs cs1 cs2]; first i_none.
    left.
    exists (us, vs, (iup :: cs1) ++ (idown :: cs2)). (* 補助スタックを使う例。 *)
        by apply: stepdip.
        
  (* add *)
  - case: vs => [cs | v1 [|v2 vs] cs]; try i_none.
    case: v1; case: v2 => n1 n2; try i_none. (* nat か bool で場合分けする。 *)
    (* nat と nat の組み合わせ以外を try i_none で片付ける。 *)
    left.
    exists (us, vn (n2 + n1) :: vs, cs).
      by apply: stepadd.
  (* sub *)
  - case: vs => [cs | v1 [|v2 vs] cs]; try i_none.
    case: v1; case: v2 => n1 n2; try i_none.
    left.
    exists (us, vn (n2 - n1) :: vs, cs).
      by apply: stepsub.
  (* mul *)
  - case: vs => [cs | v1 [|v2 vs] cs]; try i_none.
    case: v1; case: v2 => n1 n2; try i_none.
    left.
    exists (us, vn (n2 * n1) :: vs, cs).
      by apply: stepmul.
  (* eq *)
  - case: vs => [cs | v vs cs]; first i_none.
    case: v => n; try i_none.       (* nat か bool で場合分けする。 *)
    case: n.                        (* 0 か 非0 で場合分けする。 *)
    + left.
      exists (us, [:: vb true & vs], cs).
        by apply: stepeq_tt.
    + left.
      exists (us, [:: vb false & vs], cs).
        by apply: stepeq_ff.
  (* neq *)
  - case: vs => [cs | v vs cs]; first i_none.
    case: v => n; try i_none.
    case: n.
    + left.
      exists (us, [:: vb false & vs], cs).
        by apply: stepneq_ff.
    + left.
      exists (us, [:: vb true & vs], cs).
        by apply: stepneq_tt.
        
  (* 追加 up *)
  - case: vs => [cs | v vs cs]; first i_none.
    left.
    exists ([:: v & us], vs, cs).
      by apply: stepup.
  (* 追加 down *)
  - case: us => [cs | u us cs]; first i_none.
    left.
    exists (us, [:: u & vs], cs).
      by apply: stepdown.
Defined.


(* 階乗の計算 *)

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
  eapply steprtc_cons with (e2:=([::], [:: vn 1], _));
    first by apply: steppush_n.
  eapply steprtc_cons with (e2:=([::], [:: vn 4; vn 1], _));
    first by apply: steppush_n.
  eapply steprtc_cons with (e2:=([::], [:: vn 4; vn 4; vn 1], _));
    first by apply: stepdup.
  eapply steprtc_cons with (e2:=([::], [:: vb true; vn 4; vn 1], _));
    first by apply: stepneq_tt.
  (* **** *)
  eapply steprtc_cons with (e2:=([::], [:: vn 4; vn 1], _));
    first by apply: steploop_tt.
  eapply steprtc_cons with (e2:=([::], [:: vn 4; vn 4; vn 1], _));
    first by apply: stepdup.
  eapply steprtc_cons with (e2:=([::], [:: vn 4; vn 4; vn 1], _));
    first by apply: stepdip.
  eapply steprtc_cons with (e2:=([:: vn 4], [:: vn 4; vn 1], _));
    first by apply: stepup.
  eapply steprtc_cons with (e2:=([:: vn 4], [:: vn 4], _));
    first by apply: stepmul.
  eapply steprtc_cons with (e2:=([::], [:: vn 4; vn 4], _));
    first by apply: stepdown.
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 4; vn 4], _));
    first by apply: steppush_n.
  eapply steprtc_cons with (e2:=([::], [:: vn 4; vn 1; vn 4], _));
    first by apply: stepswap.
  eapply steprtc_cons with (e2:=([::], [:: vn 3; vn 4], _));
    first by apply: stepsub.
  eapply steprtc_cons with (e2:=([::], [:: vn 3; vn 3; vn 4], _));
    first by apply: stepdup.
  eapply steprtc_cons with (e2:=([::], [:: vb true; vn 3; vn 4], _));
    first by apply: stepneq_tt.
  (* **** *)
  eapply steprtc_cons with (e2:=([::], [:: vn 3; vn 4], _));
    first by apply: steploop_tt.
  eapply steprtc_cons with (e2:=([::], [:: vn 3; vn 3; vn 4], _));
    first by apply: stepdup.
  eapply steprtc_cons with (e2:=([::], [:: vn 3; vn 3; vn 4], _));
    first by apply: stepdip.
  eapply steprtc_cons with (e2:=([:: vn 3], [:: vn 3; vn 4], _));
    first by apply: stepup.
  eapply steprtc_cons with (e2:=([:: vn 3], [:: vn 12], _));
    first by apply: stepmul.
  eapply steprtc_cons with (e2:=([::], [:: vn 3; vn 12], _));
    first by apply: stepdown.
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 3; vn 12], _));
    first by apply: steppush_n.
  eapply steprtc_cons with (e2:=([::], [:: vn 3; vn 1; vn 12], _));
    first by apply: stepswap.
  eapply steprtc_cons with (e2:=([::], [:: vn 2; vn 12], _));
    first by apply: stepsub.
  eapply steprtc_cons with (e2:=([::], [:: vn 2; vn 2; vn 12], _));
    first by apply: stepdup.
  eapply steprtc_cons with (e2:=([::], [:: vb true; vn 2; vn 12], _));
    first by apply: stepneq_tt.
  eapply steprtc_cons with (e2:=([::], [:: vn 2; vn 12], _));
    first by apply: steploop_tt.
  (* **** *)
  eapply steprtc_cons with (e2:=([::], [:: vn 2; vn 2; vn 12], _));
    first by apply: stepdup.
  eapply steprtc_cons with (e2:=([::], [:: vn 2; vn 2; vn 12], _));
    first by apply: stepdip.
  eapply steprtc_cons with (e2:=([:: vn 2], [:: vn 2; vn 12], _));
    first by apply: stepup.
  eapply steprtc_cons with (e2:=([:: vn 2], [:: vn 24], _));
    first by apply: stepmul.
  eapply steprtc_cons with (e2:=([::], [:: vn 2; vn 24], _));
    first by apply: stepdown.
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 2; vn 24], _));
    first by apply: steppush_n.
  eapply steprtc_cons with (e2:=([::], [:: vn 2; vn 1; vn 24], _));
    first by apply: stepswap.
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 24], _));
    first by apply: stepsub.
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepdup.
  eapply steprtc_cons with (e2:=([::], [:: vb true; vn 1; vn 24], _));
    first by apply: stepneq_tt.
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 24], _));
    first by apply: steploop_tt.
  (* **** *)
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepdup.
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepdip.
  eapply steprtc_cons with (e2:=([:: vn 1], [:: vn 1; vn 24], _));
    first by apply: stepup.
  eapply steprtc_cons with (e2:=([:: vn 1], [:: vn 24], _));
    first by apply: stepmul.
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 24], _));
    first by apply: stepdown.
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: steppush_n.
  eapply steprtc_cons with (e2:=([::], [:: vn 1; vn 1; vn 24], _));
    first by apply: stepswap.
  eapply steprtc_cons with (e2:=([::], [:: vn 0; vn 24], _));
    first by apply: stepsub.
  eapply steprtc_cons with (e2:=([::], [:: vn 0; vn 0; vn 24], _));
    first by apply: stepdup.
  eapply steprtc_cons with (e2:=([::], [:: vb false; vn 0; vn 24], _));
    first by apply: stepneq_ff.
  eapply steprtc_cons with (e2:=([::], [:: vn 0; vn 24], _));
    first by apply: steploop_ff.
  (* **** *) 
  eapply steprtc_cons with (e2:=([::], [:: vn 24], _));
    first by apply: stepdrop.
  eapply steprtc_cons with (e2:=([::], [::], _));
    first by apply: stepdrop.
  by eapply steprtc_refl.
Qed.

(* END *)
