Require Import ssreflect ssrbool.

(**
# 第5回 集合論モデルの練習 (2014/05/04)

## 課題21 (種別:A / 締め切り : 2014/05/11)

次の定理を証明せよ。ただし、Coq.LogicおよびCoq.Setsに定義されている公理を用いても構わない。各定理について、それを証明するのに必要な公理はできるだけ弱いものに留めるのが望ましい。なお、autoやtautoなどの自動証明タクティックを用いてもよい。

*)

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
公理の追加はいらない。
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
      by case HPQ.
  (* else節の場合（(~ P) /\ R を前提とする場合） *)
  exists false.
    by case HnPR.
Qed.

(**
### 問題3

excluded_middle_informative は  Coq.Logic.ClassicalDescription の中で
定理として排中律を使って証明されているが、ここでは、直接与える。
 *)
Print decidable.                            (* fun P : Prop => {P} + {~ P} *)
Axiom excluded_middle_informative : forall P : Prop, decidable P.

(**
IF_then_else と（から）if_then_elseの関係を補題として証明できる。
*)
Lemma IF__if : forall (P Q R : Prop),
                 (IF P then Q else R) ->
                 (if is_left (excluded_middle_informative P) then Q else R).
Proof.
  move=> P Q R H.
  case (excluded_middle_informative P);
    case H => [HPQ | HnPR]; [case HPQ | case HnPR | case HPQ | case HnPR];
                by [].
Qed.

(**
補題を適用する。
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

if_then_else と（から）IF_then_elseの関係は、排中律を使わずに証明できる。
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
Axiom (EM : forall A, A \/ ~A). (* 排中律 *)

Lemma IF__or : forall P Q R,
                 (IF P then Q else R) -> Q \/ R.
Proof.
  move=> P Q R.
  case: (EM P) => [HP | HnotP];             (* EM で場合分けする。 *)
    by case=> [H1 | H2]; [left; apply H1 | right; apply H2].
Qed.

(**
ifはboolなので、排中律はいらない。
*)
Lemma if__or : forall (p : bool) (Q R : Prop),
                 (if p then Q else R) -> Q \/ R.
Proof.
  move=> p Q R.
    by case p => [HQ | HR]; [left | right].
Qed.

(**
どちらも、逆が成立しないのは、Q\/Rが成立するからといって、
Qが成立して欲しいとき(Pが成立するとき)にQが成立するとは限らないからである。
*)

(* END *)
