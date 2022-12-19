(**
論理としてのProlog (その2)
========================

@suharahiromichi

2022/12/19
 *)

From mathcomp Require Import all_ssreflect.

(**
reverse のプログラム例 #1

λPrologのstdlibから採ったので rev2 と呼びます。
*)

Section LRev.

Variable T : Type.

Variable rev2 : list T -> list T -> Prop.
Variable rev3 : list T -> list T -> list T -> Prop.

Axiom prog0 : forall L RL, rev3 L [::] RL -> rev2 L RL.
Axiom prog1 : forall X XS ACC RL, rev3 XS (X :: ACC) RL -> rev3 (X :: XS) ACC RL.
Axiom prog2 : forall RL, rev3 [::] RL RL.
      
(**
ループ不変式
*)
Lemma rev3_invariant A B : rev3 A B (rev A ++ B).
Proof.
  elim: A B prog1 prog2 => //= a A IHA B Hcons Hnil.
  apply: (Hcons).
  have -> : rev (a :: A) ++ B = rev A ++ (a :: B)
    by rewrite -[a :: A]cat1s rev_cat -catA.
  by apply: IHA.
Qed.

(**
rev3 と rev についての補題

ループ不変式からすぐに証明できます。
*)
Lemma rev3_rev L : rev3 L [::] (rev L).
Proof.
  rewrite -[rev L]cats0.
  by apply: rev3_invariant.
Qed.

(**
証明したかった定理
*)
Theorem rev2_rev L : rev2 L (rev L).
Proof.
  apply: prog0.
  by apply: rev3_rev.
Qed.

End LRev.


Section SRev.

Variable T : Type.

Variable srev : list T -> list T -> Prop.
Variable srev3 : list T -> list T -> list T -> list T -> Prop.

Axiom sprog0 : forall A B, srev3 A [::] B B -> srev A B.
Axiom sprog1 : forall A, srev3 [::] A A [::].
Axiom sprog2 : forall A B C D E F, srev3 A (B :: C) D F -> srev3 (B :: A) C D (E :: F).

End SRev.

(* END *)

  
     
