(* リレー回路 *)
(* 全加算器 Zuseの回路 の正しさの証明 *)
(*
   Prologと違って、autoのときにバックトラックが起きないから、
   正しい項を指定する必要がある。
   Coqの不得意とする問題だろうか。
*)


(*
   rly(S, S, C, C, _) :- !.
   rly(_, _, C, _, C).
*)


Inductive Sig : Set :=
| H : Sig
| L : Sig
| O : Sig.


Inductive rly : Sig -> Sig -> Sig -> Sig -> Sig -> Prop :=
| off0 : forall   c no, rly L L c c no
| off1 : forall   c no, rly H H c c no
| off2 : forall s c no, rly O s c c no
| off3 : forall s c no, rly s O c c no
| on0  : forall   c nc, rly H L c nc c
| on1  : forall   c nc, rly L H c nc c.
Hint Resolve off0 off1 off2 off3 on0 on1 : relay.


(* AND回路 *)
Inductive and_c (x y z : Sig) : Prop :=
  and_c0 : forall u v w,
    rly x L H v u -> rly y L u w z -> and_c x y z.


Check and_c H H H.


Goal and_c H H H.
Proof.
  eapply and_c0.
  apply (on0 H H).
  apply (on0 H H).
Qed.


Goal and_c H H H.
Proof.
  eapply and_c0.
  apply (on0 _ H).
  apply (on0 _ H).
Qed.


Goal and_c H L H.                           (* zはopenなので、Hでも可能 *)
Proof.
  eapply and_c0.
  apply (on0 H H).
  apply (off0 H H).
Qed.


Goal (and_c H L H /\ and_c H L L).
Proof.
  split.
  eapply and_c0.
  apply (on0 H H).
  apply (off0 H H).


  eapply and_c0.
  apply (on0 H H).
  apply (off0 H L).
Qed.


(* 出力もOPENだが、Lを加えればLになってしまう。 *)
Goal and_c O O L.
Proof.
  eapply and_c0.
  apply (off2 L H O).
  apply (off2 L O L).
Qed.


(*
%%
%% Zuseの回路 (dual-rail-carry full adder)
%%
fa(InA, InB, InC, InNotC, OutS, OutC, OutNotC) :-
        rly(InA, 0, OutNotC, I, H),
        rly(InA, 0, InNotC,  K, J),
        rly(InA, 0, InC,     J, K),
        rly(InA, 0, OutC,    N, L),
        rly(InB, 0, InNotC,  H, I),
        rly(InB, 0, OutS,    J, K), 
        rly(InB, 0, 1,       I, L),
        rly(InB, 0, InC,     L, N).
*)


Inductive fa (InA InB InC InNotC OutS OutC OutNotC : Sig ) : Prop :=
  fa0 : forall i j k l n h,
    rly InA L OutNotC i h ->
    rly InA L InNotC  k j ->
    rly InA L InC     j k ->
    rly InA L OutC    n l ->
    rly InB L InNotC  h i ->
    rly InB L OutS    j k -> 
    rly InB L H       i l ->
    rly InB L InC     l n ->
    fa InA InB InC InNotC (**) OutS OutC OutNotC.


Goal fa L H L H (**)  H L H.
Proof.
  eapply fa0.
  intros.
  apply (off0 H H).
  apply (off0 H L).
  apply (off0 L H).
  apply (off0 L H).
  apply (on0  H H).
  apply (on0  H L).
  apply (on0  H H).
  apply (on0  L H).
Qed.


Goal fa L H L H (**)  H L H.
Proof.
  eapply fa0.
  intros.
  apply (off0 _ H).
  apply (off0 _ L).
  apply (off0 _ _).
  apply (off0 _ H).
  apply (on0  _ _).
  apply (on0  _ _).
  apply (on0  _ _).
  apply (on0  _ _).
Qed.


(* テストケースを生成する *)
Inductive gen : Sig -> Sig -> Sig -> Sig -> Sig -> Sig -> Sig -> Prop :=
(*             入力     出力 *)
| gen000 : gen L L L H  L L H
| gen001 : gen L L H L  H L H
| gen010 : gen L H L H  H L H
| gen011 : gen L H H L  L H L
| gen100 : gen H L L H  H L H
| gen101 : gen H L H L  L H L
| gen110 : gen H H L H  L H L
| gen111 : gen H H H L  H H L.


Goal forall (InA InB InC InNotC OutS OutC OutNotC : Sig),
  gen InA InB InC InNotC OutS OutC OutNotC -> fa InA InB InC InNotC OutS OutC OutNotC.
Proof.
  intros.
  inversion H0.
  (* induction H0 でも同じ。*)
  
  eapply fa0.                               (* L L L *)
  intros.
  apply (off0 _ H).
  apply (off0 _ L).
  apply (off0 _ _).
  apply (off0 _ L).
  apply (off0 _ _).
  apply (off0 _ _).
  apply (off0 _ _).
  apply (off0 _ _).


  eapply fa0.                               (* L L H *)
  intros.
  apply (off0 _ L).
  apply (off0 _ H).
  apply (off0 _ _).
  apply (off0 _ H).
  apply (off0 _ _).
  apply (off0 _ _).
  apply (off0 _ _).
  apply (off0 _ _).


  eapply fa0.                               (* L H L *)
  intros.
  apply (off0 _ H).
  apply (off0 _ L).
  apply (off0 _ _).
  apply (off0 _ H).
  apply (on0  _ _).
  apply (on0  _ _).
  apply (on0  _ _).
  apply (on0  _ _).


  eapply fa0.                               (* L H H *)
  intros.
  apply (off0 _ L).
  apply (off0 _ H).
  apply (off0 _ _).
  apply (off0 _ H).
  apply (on0  _ _).
  apply (on0  _ _).
  apply (on0  _ _).
  apply (on0  _ _).


  eapply fa0.                               (* H L L *)
  intros.
  apply (on0  _ H).
  apply (on0  _ L).
  apply (on0  _ _).
  apply (on0  _ L).
  apply (off0 _ _).
  apply (off0 _ _).
  apply (off0 _ _).
  apply (off0 _ _).


  eapply fa0.                               (* H L H *)
  intros.
  apply (on0  _ H).
  apply (on0  _ H).
  apply (on0  _ _).
  apply (on0  _ L).
  apply (off0 _ _).
  apply (off0 _ _).
  apply (off0 _ _).
  apply (off0 _ _).


  eapply fa0.                               (* H H L *)
  intros.
  apply (on0 _ H).
  apply (on0 _ L).
  apply (on0 _ _).
  apply (on0 _ L).
  apply (on0 _ _).
  apply (on0 _ _).
  apply (on0 _ _).
  apply (on0 _ _).


  eapply fa0.                               (* H H H *)
  intros.
  apply (on0 _ L).
  apply (on0 _ H).
  apply (on0 _ _).
  apply (on0 _ H).
  apply (on0 _ _).
  apply (on0 _ _).
  apply (on0 _ _).
  apply (on0 _ _).
Qed.


(* END *)