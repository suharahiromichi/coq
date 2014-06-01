Require Import ssreflect ssrbool.

(**
# 第5回 集合論モデルの練習 (2014/05/04)

## 課題21 (種別:A / 締め切り : 2014/05/11)

次の定理を証明せよ。ただし、Coq.LogicおよびCoq.Setsに定義されている公理を用いても構わない。
各定理について、それを証明するのに必要な公理はできるだけ弱いものに留めるのが望ましい。
なお、autoやtautoなどの自動証明タクティックを用いてもよい。
*)

(**
## 回答

まず、問題1と問題3を解くために必要になる、排中律を定義する。
*)

(**
公理：排中律
*)
Axiom classic : forall A, A \/ ~A.          (* 排中律 *)

(**
### 問題1
*)
Lemma ABC_iff_iff :
  forall A B C : Prop, ((A <-> B) <-> C) <-> (A <-> (B <-> C)).
Proof.
admit.
Qed.  

(**
### 問題2

IF P then Q else R は、P/\Q \/ ~P/\R と定義されているので、
(P/\Q)と(~P/\R)による場合分けで解くことができる。
排中律も使用しない。
*)
Print IF_then_else.
(* = fun P Q R : Prop => P /\ Q \/ ~ P /\ R *)

Goal forall P Q R : Prop,
       (IF P then Q else R) ->
       exists b : bool, (if b then Q else R).
Proof.
  move=> P Q R.
  (* IF P then Q else R で場合分けする。 *)
  case=> [HPQ | HnPR].
  (* then節の場合（P /\ Q を前提とする場合） *)
    exists true.
      by case: HPQ.
  (* else節の場合（(~ P) /\ R を前提とする場合） *)
  exists false.
    by case: HnPR.
Qed.

(**
### excluded_middle_informative

問題3の前に excluded_middle_informative の説明をする。
これは、Coq.Logic.ClassicalDescription で定義されているので、
以下をImportすれば定理として使用できるが、ここでは説明のため。

Require Import Logic.ClassicalDescription.
*)

(**
公理：
命題 P x yを満たす x が存在するなら、関数 f:y->x (f = {x|P y x}) がある。

Pがカリー化されて解りにくいが、言いたいことはこういうことなのだろう。
これは、チャーチのiotaオペレータを弱くしたもの。(see. Coq.Logic.Description.v)
 *)
Axiom constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}.

Lemma constructive_definite_description :
  forall (A : Type) (P : A -> Prop), (exists ! x : A, P x) -> {x : A | P x}.
Proof.
  move=> A P H.
  apply constructive_indefinite_description.
  firstorder.                               (* ?? *)
Qed.

Lemma constructive_definite_descr_excluded_middle :
  (forall A : Type, forall P : A -> Prop, (exists ! x : A, P x) -> {x : A | P x}) ->
  (forall P : Prop, P \/ ~ P) ->
  forall P : Prop, {P} + {~ P}.
Proof.
  admit.                                    (* ChoiceFacts.v *)
Qed.

Theorem excluded_middle_informative : forall P : Prop, {P} + {~ P}.
Proof.
  apply
    (constructive_definite_descr_excluded_middle
       constructive_definite_description
       classic).
Defined.

(**
もちろん、自然数に対する「n = m」の特定の命題の場合は、
排中律もチャーチのiotaもなしで証明できる。
 *)
Theorem eq_nat_dec : forall (n m : nat), {n = m} + {n <> m}.
Proof.
  induction n; destruct m; auto.
  elim (IHn m); auto.
Defined.

(**
### 問題3

IF_then_else から if_then_elseの関係は証明できる。これを補題とする。
*)
Lemma IF__if : forall (P Q R : Prop),
                 (IF P then Q else R) ->
                 (if is_left (excluded_middle_informative P) then Q else R).
unfold is_left.
Proof.
  move=> P Q R H.
  case: (excluded_middle_informative P);
    case: H => [HPQ | HnPR]; [case: HPQ | case: HnPR | case: HPQ | case: HnPR];
                by [].
Qed.

(**
補題を適用すると、問題は解ける。
*)
Goal
  forall P Q R : nat -> Prop,
    (forall n, IF P n then Q n else R n) ->
    exists f : nat -> bool, (forall n, if f n then Q n else R n).
Proof.
  move=> P Q R Hn.
  exists (fun (n : nat) => is_left (excluded_middle_informative (P n))).
  move=> n.
  by apply (IF__if (P n) (Q n) (R n)).
Qed.

(**
## おまけ1

if_then_else から IF_then_elseの関係は、排中律を使わずに証明できる。
*)
Lemma if__IF : forall (p : bool) (Q R : Prop),
                 (if p then Q else R) ->
                 (IF (p = true) then Q else R).
Proof.
  rewrite /IF_then_else.
  by case=> Q R H; [left | right].
Qed.

(**
### おまけ2

IF_then_else について考えてみたが、これは弱すぎて使えなかった。

排中律を仮定すると、(IF P then Q else R) -> (Q \/ R) が成立する。
これは、Pと~Pとで場合分けできるからだ。
*)
Lemma IF__or : forall P Q R,
                 (IF P then Q else R) -> Q \/ R.
Proof.
  move=> P Q R.
  case: (classic P) => [HP | HnotP];        (* 排中律で場合分けする。 *)
    by case=> [H1 | H2]; [left; apply H1 | right; apply H2].
Qed.

(**
ifはboolなので、排中律はいらない。
*)
Lemma if__or : forall (p : bool) (Q R : Prop),
                 (if p then Q else R) -> Q \/ R.
Proof.
  move=> p Q R.
    by case: p => [HQ | HR]; [left | right].
Qed.

(**
どちらも、逆が成立しないのは、Q\/Rが成立するからといって、
Qが成立して欲しいとき(Pが成立するとき)にQが成立するとは限らないからである。
*)

(* END *)
