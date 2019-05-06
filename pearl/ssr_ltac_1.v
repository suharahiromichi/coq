(**
Mathcomp で便利な Ltac 定義 (Proof Pearl ##4)
======
2019/05/06

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_ltac_1.v

 *)

(**
# 説明

*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Negative.

  (* 否定を意味する前提を正規なかたちにする。 *)
  (* 一般のライプニッツの等式については、変換できるとは限らないので、
     nat の不等式については、別に扱う。 *)
  
  Ltac neg2not :=
    repeat
      match goal with
      | [ H : _ <> true                 |- _ ] => move/negP in H
      | [ H : _ = false                 |- _ ] => move/negP in H
      | [ H : ~ _                       |- _ ] => move/negP in H
      | [ H : is_true (_ != true)       |- _ ] => move/eqP in H
      | [ H : is_true (_ != _)          |- _ ] => move/eqP in H
      | [ H : is_true (_ == false)      |- _ ] => rewrite eqbF_neg in H
      | [ H : is_true (~~ (_ == true))  |- _ ] => rewrite Bool.negb_involutive in H
      | [ H : is_true (~~ (_ == _))     |- _ ] => rewrite Bool.negb_involutive in H
      | [ H : is_true (~~ (_ != false)) |- _ ] => rewrite Bool.negb_involutive in H
      | [ H : is_true (~~ (~~ _))       |- _ ] => rewrite Bool.negb_involutive in H
(*    | [ H : is_true (~~ _)            |- _ ] => move/negP in H *)
      end.
  
  (* 前提 <> からは変換できない。 *)
  Goal forall (a b : nat), a != b -> a <> b.
    move=> a b H1.
      by neg2not.
  Qed.

  Goal forall (b : bool), ~ b -> ~~ b.
  Proof.
    move=> b H1.
      by neg2not.
  Qed.

  Goal forall (b : bool), ~~ (b != false) -> ~~ b.
  Proof.
    move=> b H1.
      by neg2not.
  Qed.

  Goal forall (b : bool), ~~ ~~ ~~ b -> ~~ b.
  Proof.
    move=> b H1.
      by neg2not.
  Qed.
  
  Goal forall (b : bool), b <> true -> ~~ b.
  Proof.
    move=> b H1.
      by neg2not.
  Qed.
  
  Goal forall (b : bool), b = false -> ~~ b.
  Proof.
    move=> b H1.
      by neg2not.
  Qed.
  
  Goal forall (b : bool), b != true -> ~~ b.
  Proof.
    move=> b H1.
      by neg2not.
  Qed.
  
  Goal forall (b : bool), b == false -> ~~ b.
    move=> b H1.
      by neg2not.
  Qed.
  
End Negative.


Section Inequality.
  
  Ltac ineq2not :=
    repeat
      match goal with
      | [ H : is_true ((_ == _) == false)  |- _ ] => move/(elimT eqP) in H
      | [ H : (_ == _) = false             |- _ ] => move/(elimF eqP) in H
      | [ H : is_true (_ != _)             |- _ ] => move/(elimN eqP) in H
      | [ H : ~ (is_true (_ == _))         |- _ ] => move/(introT negP) in H
      | [ H : (is_true (~~ (_ == _)))      |- _ ] => rewrite Bool.negb_involutive in H

      | [ H : is_true ((_ != _) == false)  |- _ ] => move/eqP in H
      | [ H : (_ != _) = false             |- _ ] => move/(elimNf eqP) in H
      | [ H : is_true (_ == _)             |- _ ] => move/eqP in H
      | [ H : ~ (is_true (_ != _))         |- _ ] => move/negP in H
      | [ H : (is_true (~~ (_ != _)))      |- _ ] => rewrite Bool.negb_involutive in H
      end.


  (* おまけのおまけ。不等号は5種類ある。 *)
  (* ただし、= false を <> true にしたののは、上を参照のこと。 *)
  
  Goal forall (x y : nat), (x == y) == false -> x <> y.
    move=> x y H1.
      by ineq2not.
  Qed.
  
  Goal forall (x y : nat), (x == y) = false -> x <> y.
    move=> x y.
    move=> H1.
      by ineq2not.
  Qed.
  
  Goal forall (x y : nat), (x != y) -> x <> y. (* negb eqb *)
    move=> x y H.
    ineq2not.
    done.
  Qed.
  
  (* これだけ Prop -> bool であることに注意。 *)
  Goal forall (x y : nat), ~ (x == y) -> x <> y. (* not eqb *)
    move=> x y H.
    ineq2not.
    done.
  Qed.
  
  (* ***** *)
  
  Goal forall (x y : nat), (x != y) == false -> x = y.
    move=> x y H.
      by ineq2not.
  Qed.
  
  Goal forall (x y : nat), (x != y) = false -> x = y.
    move=> x y H.
      by ineq2not.
  Qed.
  
  Goal forall (x y : nat), (x == y) -> x = y.
    move=> x y H.
      by ineq2not.
  Qed.
  
  Goal forall (x y : nat), ~ (x != y) -> x = y.
    move=> x y H.
      by ineq2not.
  Qed.
  
  Goal forall (x y : nat), ~~ (x != y) -> x = y.
    move=> x y H.
      by ineq2not.
  Qed.
  
  Section TEST.
    
    Variable x y : nat.
    
    Check elimT (@eqP _ x y) : x == y -> x = y.
    Check elimF (@eqP _ x y) : (x == y) = false -> x <> y.
    Check elimN (@eqP _ x y) : x != y -> x <> y.
    Check elimNf (@eqP _ x y) : (x != y) = false -> x = y.
    
    Check introT (@eqP _ x y) : x = y -> x == y.
    Check introF (@eqP _ x y) : x <> y -> (x == y) = false.
    Check introN (@eqP _ x y) : x <> y -> x != y.
    Check introNf (@eqP _ x y) : x = y -> (x != y) = false.
    
    Check elimTn.               (* reflect 述語中に否定が含まれる場合。 *)
    Check elimFn.
    
  End TEST.
  
End Inequality.

(* END *)


