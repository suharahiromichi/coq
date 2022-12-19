(**
論理としてのProlog (その2)
========================

@suharahiromichi

2022/12/19
 *)

From mathcomp Require Import all_ssreflect.

Section Rev.

Variable T : Type.

Variable rev2 : list T -> list T -> Prop.
Variable rev3 : list T -> list T -> list T -> Prop.

(**
ホーン節の部分は以下のようになります。
ここでは便宜的にDefinitionでまとめていますが、論理式としての意味は変わりません。
*)
Axiom prog0 :
  (forall L RL, rev3 L [::] RL -> rev2 L RL)
  /\
    (forall X XS ACC RL, rev3 XS (X :: ACC) RL -> rev3 (X :: XS) ACC RL)
  /\
    (forall RL, rev3 [::] RL RL).
      
(**
# 証明1
*)
Lemma rev0 : @rev T [::] = [::].
Proof.
  done.
Qed.

Lemma test (A B : seq T) : rev3 A B (rev A ++ B).
Proof.
  case: prog0 => [_ [Hcons Hnil]].
  elim: A B => //= a A IHA B.
  apply: (Hcons).
  have -> : rev (a :: A) ++ B = rev A ++ (a :: B)
    by rewrite -[a :: A]cat1s rev_cat -catA.
  by apply: IHA.
Qed.

Lemma test2 (A : seq T) : rev3 A [::] (rev A).
Proof.
  rewrite -[rev A]cats0.
  by apply: test.
Qed.

Goal forall L, rev2 L (rev L).
Proof.
  case: prog0 => [Hp [Hcons Hnil]] L.
  apply: Hp.
  elim: L => [| a s IHs].
  - by rewrite rev0.
  - by apply: test2.
Qed.

End Rev.

(* END *)
  
