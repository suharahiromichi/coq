(** Brainfuck / Brainf*ck *)
(** ループ不変式を証明してみる。 *)

(** Brainfuckの参考 : 
- https://www.slideshare.net/KMC_JP/brainfck
- https://www.codingame.com/playgrounds/50426/getting-started-with-brainfuck/welcome
 *)

(** @suharahiromicihi *)
(** 2019_11_01 *)

From mathcomp Require Import all_ssreflect.
Require Import ssrclosure.
Require Import ssromega.
(* Require Import ssrinv. *)
(* Require Import ssrstring. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive inst : Set :=                     (* c *)
| ileft                                     (* < *)
| iright                                    (* > *)
| iinc                                      (* + *)
| idec                                      (* - *)
| iin                                       (* , *)
| iout                                      (* . *)
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
    + case: ins => [|x' ins']; by eexists; constructor. (* . *)
    + by eexists; constructor.                          (* , *)
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

(* ******* *)
(* samples *)
(* ******* *)

(* *********** *)
(* Sum numbers *)
(* *********** *)
(**
[    while B is not null
  -  decrease B
  <+ go to A and increase
  >  go back to B
]    loop
 *)
Definition add := [:: iloop [:: idec; iright; iinc; ileft]]. (* [-<+>] *)

Goal (add, [::], 4, [:: 3], [::], [::]) |=>* ([::], [::], 0, [:: 7], [::], [::]).
Proof.
  by do !stepstep.
Qed.

Lemma addition_invariant (n m : nat) :
  (add, [::], n, [:: m], [::], [::]) |=>* ([::], [::], 0, [:: n + m], [::], [::]).
Proof.
  elim: n m => [| n IHn] m.
  - by stepstep.
  - do 5!stepstep.                          (* ループの中身を1巡する。 *)
    rewrite succnK addSnnS /= -/add.
      by apply: IHn.
Qed.

Lemma addition_invariant' (A B A' B' X : nat) :
  A + B = X ->                            (* ループ不変式 *)
  B' = 0 -> A' = X ->                     (* 終了条件とループ不変式 *)
  (add, [::], B, [:: A], [::], [::]) |=>* ([::], [::], B', [:: A'], [::], [::]).
Proof.
  move=> H H1 H2.
  subst.
  elim: B A => [| B IHB] A.
  - rewrite addn0.
      by stepstep.
  - do 5!stepstep.                          (* ループの中身を1巡する。 *)
    rewrite succnK /= -/add.
    have -> : A + B.+1 = A.+1 + B by ssromega.
      by apply: IHB.
Qed.

(* **************** *)
(* Subtract numbers *)
(* **************** *)
(**
[    while B is not null
  -  decrease B
  <- go to A and increase
  >  go back to B
]    loop
 *)
Definition sub := [:: iloop [:: iright; idec; ileft; idec]]. (* [-<->] *)

Goal (sub, [::], 3, [:: 7], [::], [::]) |=>* ([::], [::], 0, [:: 4], [::], [::]).
Proof.
  by do !stepstep.
Qed.

(* m < n であっても、値が0になるだけなので、前提に条件は不要である。 *)
Lemma subtract_invariant (n m : nat) :
  (sub, [::], n, [:: m], [::], [::]) |=>* ([::], [::], 0, [:: m - n], [::], [::]).
Proof.
  elim: n m => [| n IHn] m.
  - stepstep.
      by rewrite subn0.
  - do 5!stepstep.                       (* ループの中身を1巡する。 *)
    rewrite succnK /= -/sub.
    have -> : m - n.+1 = m.-1 - n by ssromega.
      by apply: IHn.
Qed.

Lemma subtract_invariant' (A B A' B' X : nat) :
  A - B = X ->                              (* ループ不変式 *)
  B' = 0 -> A' = X ->                       (* 終了条件とループ不変式 *)
  (sub, [::], B, [:: A], [::], [::]) |=>* ([::], [::], B', [:: A'], [::], [::]).
Proof.
  move=> H H1 H2.
  subst.
  elim: B A => [| B IHB] A.
  - stepstep.
      by rewrite subn0.
  - do 5!stepstep.                       (* ループの中身を1巡する。 *)
    rewrite succnK /= -/sub.
    have -> : A - B.+1 = A.-1 - B by ssromega.
      by apply: IHB.
Qed.

(* **************************** *)
(* Move value (aka pseudo-copy) *)
(* **************************** *)
(**
[    while A is not null
  -  decrease A
  >+ increase target
  <  go back to A
]    loop
*)
Definition mv := [:: iloop [:: idec; iright; iinc; ileft]]. (* [->+<] *)

Goal (mv, [::], 2, [::], [::], [::]) |=>* ([::], [::], 0, [::2], [::], [::]).
Proof.
  do 5!stepstep.
  do 5!stepstep.
  stepstep.
  done.
Qed.

Lemma move_invariant (n m : nat) :
  (mv, [::], n, [:: m], [::], [::]) |=>* ([::], [::], 0, [:: n + m], [::], [::]).
Proof.
  elim: n m => [| n IHn] m.
  - stepstep.
      by rewrite add0n.
  - do 5!stepstep.
    rewrite succnK /= -/mv.
    have -> : n.+1 + m = n + m.+1 by ssromega.
      by apply: IHn.
Qed.

Lemma move_invariant' (A B A' B' X : nat) :
  A + B = X ->                              (* ループ不変式 *)
  A' = 0 -> B' = X ->                       (* 終了条件とループ不変式 *)
  (mv, [::], A, [:: B], [::], [::]) |=>* ([::], [::], A', [:: B'], [::], [::]).
Proof.
  move=> H H1 H2.
  subst.
  elim: A B => [| A IHA] B.
  - stepstep.
      by rewrite add0n.
  - do 5!stepstep.
    rewrite succnK /= -/mv.
    have -> : A.+1 + B = A + B.+1 by ssromega.
      by apply: IHA.
Qed.

(* *********** *)
(* Copy value *)
(* *********** *)
(**
[    while A is not null
  -  decrease A
  >+ increase 1st next cell
  >+ increase 2nd next cell
  <<  go back to A
]
 *)
Definition cp :=
  [:: iloop [:: idec; iright; iinc; iright; iinc; ileft; ileft]]. (* [->+>+<<] *)

Goal (cp, [::], 2, [::0], [::], [::]) |=>* ([::], [::], 0, [::2;2], [::], [::]).
Proof.
  do 8!stepstep.
  do 8!stepstep.
  stepstep.
  done.
Qed.

Lemma copy_invariant (n m : nat) :
  (cp, [::], n, [:: m; m], [::], [::]) |=>* ([::], [::], 0, [:: n+m; n+m], [::], [::]).
Proof.
  case: n m.
  - move=> m.
    stepstep.
      by rewrite add0n.
  - elim=> [| n IHn] m.
    + do 8!stepstep.
      stepstep.
        by rewrite add1n.
    + do 8!stepstep.
      rewrite succnK /= -/cp.
      have -> : n.+2 + m = n.+1 + m.+1 by ssromega.
        by apply: IHn.
Qed.

Lemma copy_value (n : nat) :
  (cp, [::], n, [::0; 0], [::], [::]) |=>* ([::], [::], 0, [:: n; n], [::], [::]).
Proof.
  rewrite -{2}[n]addn0 -{3}[n]addn0.
    by apply: copy_invariant.
Qed.

Lemma copy_invariant' (A B C A' B' C' X : nat) :
  A + B = X -> B = C ->                     (* ループ不変式 *)
  A' = 0 -> B' = X -> B' = C' ->             (* 終了条件 *)
  (cp, [::], A, [:: B; C], [::], [::]) |=>* ([::], [::], A', [:: B'; C'], [::], [::]).
Proof.
  move=> H H' H1 H2 H3.
  subst.
  case: A C.
  - move=> C.
    stepstep.
      by rewrite add0n.
  - elim=> [| A IHA] C.
    + do 8!stepstep.
      stepstep.
        by rewrite add1n.
    + do 8!stepstep.
      rewrite succnK /= -/cp.
      have -> : A.+2 + C = A.+1 + C.+1 by ssromega.
        by apply: IHA.
Qed.

(* ******* *)
(* 定数倍  *)
(* ******* *)
Definition mulc :=                          (* [>+++++<-] *)
  [:: iloop [:: iright;  iinc; iinc; iinc; iinc; iinc;  ileft; idec]].

Goal (mulc, [::], 3, [::], [::], [::]) |=>* ([::], [::], 0, [::15], [::], [::]).
Proof.
  do 9!stepstep.
  do 9!stepstep.
  do 9!stepstep.
    by stepstep.
Qed.

Lemma multiply_const_invariant (n m : nat) :
  (mulc, [::], n, [:: m], [::], [::]) |=>* ([::], [::], 0, [:: n * 5 + m], [::], [::]).
Proof.
  elim: n m => [|n IHn] m.
  - stepstep.
      by rewrite mul0n.
  - do 9!stepstep.                      (* ループの中身を一巡する。 *)
    rewrite /= -/mulc.
    have -> : n.+1 * 5 + m = n * 5 + (m + 5) by ssromega.
    have -> : m.+1.+4 = m + 5 by ssromega.
      by apply: IHn.                        (* IHn (m + 5) *)
Qed.    

Lemma multiply_const (n : nat) :
  (mulc, [::], n, [:: 0], [::], [::]) |=>* ([::], [::], 0, [:: n * 5], [::], [::]).
Proof.
  rewrite -[n * 5]addn0.
    by apply: multiply_const_invariant. 
Qed.


(* **************** *)
(* Multiply numbers *)
(* **************** *)
(**
[       while m is not null
  >[    while n is not null
    -   decrease n
    >+  increase o
    >+  increase p
  <<]   loop
  >[    while o is not null
    -   decrease o
    <+  increase n
  >]    loop
  <<-   decrease m
]       loop
 *)
Definition mul :=                           (* [>[->+>+<<]>[-<+>]<<-] *)
  [:: iloop [:: iright;
               iloop [:: idec; iright; iinc; iright; iinc; ileft; ileft];
               iright;
               iloop [:: idec; ileft; iinc; iright];
               ileft; ileft; idec]].

Goal (mul, [::], 3, [::5;0;0], [::], [::]) |=>* ([::], [::], 0, [::5;0;15], [::], [::]).
Proof.
  stepstep.
  
  stepstep.                                 (* 73 *)
  do 8!stepstep.
  do 8!stepstep.
  do 8!stepstep.
  do 8!stepstep.
  do 8!stepstep.
  stepstep.
  stepstep.
  do 5!stepstep.
  do 5!stepstep.
  do 5!stepstep.
  do 5!stepstep.
  do 5!stepstep.
  do 5!stepstep.
  
  do 73!stepstep.
  do 73!stepstep.
  
  done.
Qed.

(* invariant : m, n, p=Bx(A-m) + (B-n), o= B-n *)
(* terminal : Memory: 0, B, 0 , AxB *)

Lemma multiply_invariant (m n o p m' n' o' p' A B : nat) :
  p = B * (A - m) + (B - n) -> o = B - n -> (* ループ不変式 *)
  m' = 0 -> n' = B -> o' = 0 -> p' = A * B -> (* 終了条件とループ不変式 *)
  (mul, [::], m, [:: n; o; p], [::], [::])
    |=>* ([::], [::], m', [:: n'; o'; p'], [::], [::]).
Proof.
  move=> H H' H1 H2 H3 H4.
  subst.
(**
  m, n, A, B : nat
  ============================
  (mul, [::], m, [:: n; B - n; B * (A - m) + (B - n)], [::], [::])
  |=>* ([::], [::], 0, [:: B; 0; A * B], [::], [::])
*)
  elim: m n A B.
  - move=> n A B.
    rewrite subn0.
    
   elim: (B - n).          (* n は B から減っていく帰納法が必要か？ *)
    (* i = B - n, i = 0.... *)
    (* n = B - i, n = B.... *)
    + admit.
    + 
Admitted.

(* END *)


(* ****************************** *)
(* 値のコピー [>+>+<<-]>>[<<+>>-] *)
(* ****************************** *)
(* 意図どおりは動作しない。 *)
(*
Definition copy := [:: iloop [:: iright; iinc; iright; iinc; ileft; ileft; idec];
                      iright; iright;
                        iloop [:: ileft; ileft; iinc; iright; iright; idec]].
 *)
