(**
論理としてのProlog (その2)
========================

@suharahiromichi

2022/12/19
 *)

From mathcomp Require Import all_ssreflect.

(**
reverse のプログラム例 #1

λPrologのstdlibから採ったので lrev と呼びます。
*)

Section LRev.

Variable T : Type.

Variable lrev : list T -> list T -> Prop.
Variable lrev3 : list T -> list T -> list T -> Prop.

Axiom lprog : forall L RL, lrev3 L [::] RL -> lrev L RL.
Axiom lprog1 : forall X XS ACC RL, lrev3 XS (X :: ACC) RL -> lrev3 (X :: XS) ACC RL.
Axiom lprog2 : forall RL, lrev3 [::] RL RL.
      
(**
ループ不変式
*)
Lemma lrev_invariant A B : lrev3 A B (rev A ++ B).
Proof.
  elim: A B lprog1 lprog2 => //= a A IHA B Hcons Hnil.
  apply: (Hcons).
  have -> : rev (a :: A) ++ B = rev A ++ (a :: B)
    by rewrite -[a :: A]cat1s rev_cat -catA.
  by apply: IHA.
Qed.

(**
rev3 と rev についての補題

ループ不変式からすぐに証明できます。
*)
Lemma lrev3_rev L : lrev3 L [::] (rev L).
Proof.
  rewrite -[rev L]cats0.
  by apply: lrev_invariant.
Qed.

(**
証明したかった定理
*)
Theorem lrev_rev L : lrev L (rev L).
Proof.
  apply: lprog.
  by apply: lrev3_rev.
Qed.

End LRev.

(* END *)
  
     
