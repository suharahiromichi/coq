(**
騎士と悪党のパズル

https://lean-ja.github.io/lean-by-example/Tutorial/Exercise/KnightAndKnave.html

https://philosophy.hku.hk/think/logic/knights.php
 *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section knight_and_knave.
  (** その島の住民を表す型 *)
  Variable Islander : finType.
  Variable Knight : pred Islander.
  
  Definition islander := [set: Islander].   (* 全集合 *)
  
  (** Islander の部分集合として定義した騎士の全体 *)
  Definition knight := [set x in islander | Knight x].
  Check knight \subset islander.
  
  (** Islander の部分集合として定義した悪党の全体 *)
  Definition knave := [set x in islander | ~~ Knight x].
  Check knave \subset islander.
  
  (** 人は騎士か悪党のどちらか *)
  Lemma knight_or_knave (p : Islander) : (p \in knight) || (p \in knave).
  Proof.
    rewrite !inE.
    by case: (Knight p).
  Qed.
  
  (** 人が騎士かつ悪党であることはない *)
  Lemma knight_ne_knave (p : Islander) : ~~((p \in knight) && (p \in knave)).
  Proof.
    rewrite !inE.
    by case: (Knight p).
  Qed.
  
  (** 騎士でないことと悪党であることは同値 *)
  Lemma of_not_knight {p : Islander} : (p \notin knight) = (p \in knave).
  Proof.
    rewrite !inE.
    by case: (Knight p).
  Qed.
  
  (** 悪党でないことと騎士であることは同値 *)
  Lemma of_not_knave {p : Islander} : (p \notin knave) = (p \in knight).
  Proof.
    rewrite !inE.
    by case: (Knight p).
  Qed.

(**
これでゾーイとメルが島民であり、騎士か悪党かのどちらかであるということは次のように表現できます。
 *)
  (** ゾーイ *)
  Variable zoey : Islander.
  (** メル *)
  Variable mel : Islander.

  Goal zoey \in islander.
  Proof. done. Qed.
  
  Goal mel \in islander.
  Proof. done. Qed.

(**
正直者であるとか嘘つきであるということを表現するために、
誰がなんと発言したかを表現するための関数を用意します。
その上で、それぞれの発言を愚直に形式化していきます。
 *)
  (** p さんが body という命題を話したという事実を表す命題 *)
  Variable islander_say : Islander -> bool -> bool.
  
  (** 騎士の発言内容はすべて真実 *)
  Axiom statement_of_knight
    : forall (p : Islander) (h : p \in knight) (say : bool), islander_say p say = say.

  (** 悪党の発言内容はすべて偽 *)
  Axiom statement_of_knave
    : forall (p : Islander) (h : p \in knave) (say : bool), islander_say p say = ~~say.

  (** ゾーイは「メルは悪党だ」と言った *)
  Axiom zoey_says : islander_say zoey (mel \in knave).

  (** メルは「ゾーイもメルも悪党ではない」と言った *)
  Axiom mel_says : islander_say mel ((zoey \notin knave) && (mel \notin knave)).

(*
  (**`p` が騎士か悪党のどちらなのか知っていることを表す型 *)
  Inductive Solution (p : Islander) : Type :=
  | isKnight : p \in knight -> Solution p
  | isKnave  : p \in knave  -> Solution p.
*)

  (** ゾーイは悪党ではない *)
  Lemma zoey_is_not_knave : zoey \notin knave.
  Proof.
    apply/negP.
    move=> zoey_is_knave.
    
    have mel_is_knight : mel \in knight.
    {
      have H := statement_of_knave zoey_is_knave (mel \in knave).
      by rewrite -of_not_knave -H zoey_says.
    }.
    
    have mel_says_truth :=
      statement_of_knight mel_is_knight ((zoey \notin knave) && (mel \notin knave)).
    
    move/esym in mel_says_truth.
    rewrite mel_says in mel_says_truth.
    move/andP in mel_says_truth.
    move: mel_says_truth.
    case=> zoey_not_knave mel_not_kave.
    (* zoey_is_knave of_not_knave mel_is_knight in mel_says_truth. *)
    
    have zony_is_knight : zoey \in knight.
    {
      rewrite -of_not_knave.
      by rewrite zoey_not_knave.
    }
    
    move/negP in zoey_not_knave.
    apply: zoey_not_knave.
    done.
  Qed.
  
  Theorem zoey_is_knight : zoey \in knight.
  Proof.
    rewrite -of_not_knave.
    by rewrite zoey_is_not_knave.
  Qed.

  (** メルは悪党である。 *)
  Theorem mel_is_knave : mel \in knave.
  Proof.
    have := statement_of_knight zoey_is_knight (mel \in knave).
    by rewrite zoey_says => <-.
  Qed.

End knight_and_knave.

(* END *)
