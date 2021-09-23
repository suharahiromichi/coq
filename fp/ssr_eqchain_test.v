(**
連鎖記法の導入と使用例
========================

@suharahiromichi

2020/09/23
 *)

(**
# EqChain について

等号「=」についての連鎖記法を導入します。

- Julien Tesson, Hideki Hashimoto, Zhenjiang Hu, Frederic Loulergue,
and Masato Takeichi, "Program Calculation in Coq"

- 村田康佑 「定理証明支援系Coq によるデータ型汎用なプログラム運算」
§2.2 鎖状記法の設計と実装

- https://github.com/muratak17/Recursion-Schemes-in-Coq
eqchain.v
 *)

(* ******************* *)
(** eqchan.v ここから。 *)
(* ******************* *)
Require Import Coq.Program.Basics.

Module EqChain.

(* state for memorizing direction of equational reasoning *)

Inductive equational_reasoning_direction : Type :=
  Rightwards : equational_reasoning_direction
| Leftwards  : equational_reasoning_direction.

Inductive direction (cs : equational_reasoning_direction) : Prop :=
  state : direction cs.

(* tactic for obvious rewriting *)

Ltac obvious := (simpl; reflexivity) + easy + auto.

(* rewriting *)

Ltac eq_rewrite_l c t :=
  let Hre := fresh "H" in(
    match goal with
    | [ |- _ ?l _ ] =>
      ( assert (l = c) as Hre );
      [ t; obvious | idtac ];
      (erewrite Hre at 1) +                 (* coq の rewrite *)
      (match goal with
       | [ H : _ c c |- _] => idtac
       end);
      clear Hre
    end
  ).

Lemma flipgoal1 :
  forall {A B : Type} (R : A -> B -> Prop) (x : A) (y : B),
    flip R y x -> R x y. 
Proof.
  easy.
Qed.

Lemma flipgoal2 :
  forall {A B : Type} (R : A -> B -> Prop) (x : A) (y : B),
    R x y -> flip R y x. 
Proof.
  easy.
Qed.

End EqChain.

Tactic Notation "eqChain_add_state" constr(cs) :=
  let statename := fresh "d" in (
    pose ( statename := EqChain.direction cs )).

Tactic Notation "eqChain_set_state" constr(cs) :=
  match goal with
  | [d := EqChain.direction cs : Prop |- _] => idtac
  | [d := EqChain.direction _  : Prop |- _] => fail 1 "illegal direction"
  | _ => eqChain_add_state cs
  end.

Ltac eqChain_flipgoal :=
  match goal with
  | [ |- flip _ _ _ ] => apply EqChain.flipgoal2
  | [ |- _ _ _ ] => apply EqChain.flipgoal1
  end.

Ltac eqChain_eq_rewrite_r c t :=
  match goal with
  | [ |- ?R _ _ ] =>
    eqChain_flipgoal;
    EqChain.eq_rewrite_l c t;
    eqChain_flipgoal
  end.

(**
## 公開される Notation

最低限のTacticのみ公開しています。
*)

Tactic Notation (at level 2) "Left" "=" constr(c) "{" tactic(t) "}" :=
  EqChain.eq_rewrite_l c t ; eqChain_set_state EqChain.Rightwards.

Tactic Notation (at level 2) "=" constr(c) "{" tactic(t) "}" :=
  match goal with
  | [_ := EqChain.direction EqChain.Rightwards : Prop |- _] => EqChain.eq_rewrite_l c t
  | [_ := EqChain.direction EqChain.Leftwards  : Prop |- _] => eqChain_eq_rewrite_r c t
  end.

Tactic Notation (at level 2) "=" "Right" "{" tactic(t) "}" :=
  match goal with
  | [_ := EqChain.direction EqChain.Rightwards : Prop |- _ _ ?r] =>
    EqChain.eq_rewrite_l r t; reflexivity
  end.
(* ******************* *)
(** eqchan.v ここまで *)
(* ******************* *)

(**
# 例
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Section Test.
(**
## 簡単な例
*)
  
  Goal 1 = 1.
  Proof.
    Left
    = (1)   {idtac}.
    = Right {idtac}.
  Qed.
  
  Goal 1 + 0 = 1.
  Proof.
    Left
    = (1)   {rewrite addn0}.
    = Right {done}.
  Qed.

(**
## すこし大きな例

普通の証明
*)
  Lemma square_eq' a b : (a + b) * (a + b) = a * a + 2 * a * b + b * b.
  Proof.
    rewrite [LHS]mulnDr.
    rewrite 2![in LHS]mulnDl.
    rewrite [LHS]addnA.
    rewrite [b * a in LHS]mulnC.
    rewrite -2![LHS]addnA.
    rewrite [(a * b + (a * b + b * b)) in LHS]addnA.
    rewrite [a * b + a * b in LHS]addnn.
    rewrite [in LHS]doubleMl.
    rewrite -[in LHS]mul2n.
    rewrite [LHS]addnA.
    done.
  Qed.

(**
have の連鎖で証明する例。左辺の書き換えを追えるが、転記が必要である。
*)
  Lemma square_eq'' a b : (a + b) * (a + b) = a * a + 2 * a * b + b * b.
  Proof.
    have -> : (a + b) * (a + b) = (a + b) * a + (a + b) * b
      by rewrite [LHS]mulnDr.
    have -> : (a + b) * a + (a + b) * b = a * a + b * a + (a * b + b * b)
      by rewrite 2![in LHS]mulnDl.
    have -> : a * a + b * a + (a * b + b * b) = a * a + b * a + a * b + b * b
      by rewrite [LHS]addnA.
    have -> : a * a + b * a + a * b + b * b = a * a + a * b + a * b + b * b
      by rewrite [in LHS]mulnC.
    have -> : a * a + a * b + a * b + b * b = a * a + (a * b + (a * b + b * b))
      by rewrite -2![LHS]addnA.
    have -> : a * a + (a * b + (a * b + b * b)) = a * a + (a * b + a * b + b * b)
      by rewrite [(a * b + (a * b + b * b))]addnA.
    have -> : a * a + (a * b + a * b + b * b) = a * a + ((a * b).*2 + b * b)
      by rewrite addnn.
    have -> : a * a + ((a * b).*2 + b * b) = a * a + (a.*2 * b + b * b)
      by rewrite doubleMl.
    have -> : a * a + (a.*2 * b + b * b) = a * a + (2 * a * b + b * b)
      by rewrite -mul2n.
    have -> : a * a + (2 * a * b + b * b) = a * a + 2 * a * b + b * b
      by rewrite addnA.
    done.
  Qed.

(**
等号による連鎖記法の例
*)  
  Lemma square_eq a b : (a + b) * (a + b) = a * a + 2 * a * b + b * b.
  Proof.
    Left
    = ((a + b) * a + (a + b) * b)         {rewrite mulnDr}.
    = (a * a + b * a + (a * b + b * b))   {rewrite 2!mulnDl}.
    = (a * a + b * a + a * b + b * b)     {rewrite addnA}.
    = (a * a + a * b + a * b + b * b)     {rewrite [a * b]mulnC}.
    = (a * a + (a * b + (a * b + b * b))) {rewrite -2!addnA}.
    = (a * a + (a * b + a * b + b * b))   {rewrite [(a * b + (a * b + b * b))]addnA}.
    = (a * a + ((a * b).*2 + b * b))      {rewrite addnn}.
    = (a * a + (a.*2 * b + b * b))        {rewrite doubleMl}.
    = (a * a + (2 * a * b + b * b))       {rewrite -mul2n}.
    = (a * a + 2 * a * b + b * b)         {rewrite addnA}.
    = Right                               {done}.
  Qed.
  
End Test.

(**
## 整数の例
*)
Section Test2.

  Import GRing.Theory.        (* mulrA などを使えるようにする。 *)
  Import Num.Theory.          (* unitf_gt0 などを使えるようにする。 *)
  Import intZmod.             (* addz など *)
  Import intRing.             (* mulz など *)
  Open Scope ring_scope.      (* 環の四則演算を使えるようにする。 *)

  Lemma mulKq' (p q : rat) : 0 < p -> (p * q) / p = q.
  Proof.
    move=> Hp.
    rewrite [p * q]mulrC.                   (* q * p / p = q *)
    rewrite -mulrA.                         (* q * (p / p) = q *)
    rewrite divrr; last by rewrite unitf_gt0. (* q * 1 = q *)
      by rewrite mulr1.
  Qed.
  
  Lemma mulKq (p q : rat) : 0 < p -> (p * q) / p = q.
  Proof.
    move=> Hp.
    Left
    = (q * p / p)   {rewrite [p * q]mulrC}.
    = (q * (p / p)) {rewrite -mulrA}.
    = (q * 1)       {rewrite divrr; last by rewrite unitf_gt0}. (* サブゴールは作らぬ *)
    = Right         {by rewrite mulr1}.
  Qed.

End Test2.

(* END *)
