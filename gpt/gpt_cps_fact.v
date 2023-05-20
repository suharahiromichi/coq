(**
ChatGPTにCoqのコードを書かせてみた
==============================
2023/05/20


@suharahiromichi


ChatGPTにCoqのコードを書かせてみました。
演習問題によくあるように Admitted を含む Standard Coq のコードを完全なものにしてもらいました。


具体的には、以下の``質問``の次の``これは``から``End Question``までを ChatGPTに与えました。
その結果を``回答``以下に貼り付けてあります。
ただし、ChatGPTの回答は間違いが（simplのやりすぎと、rewriteの順番と方向の間違い）があったので、
それは、コメントして修正しています。
証明をより短く修正することも可能ですが、それは考慮していません。


この結果をどう考えるかは、みなさんにお任せします。
*)

(**
# 質問

これは、定理証明支援系Coqのコードです。
以下のAdmittedを解消して、完全な証明にしてください。
また、Module名のQuestionをAnserに変えてください。
 *)
Module Question.

Fixpoint fact (n : nat) : nat :=
  match n with
    | 0 => 1
    | (S n') => n * fact n'
  end.
Eval cbv in fact 6.                         (* 720 *)

Fixpoint fact_cps (n : nat) (cont : nat -> nat) : nat :=
  match n with
    | 0 => cont 1
    | (S n') => fact_cps n' (fun (a : nat) => cont (n * a))
  end.
Eval cbv in fact_cps 6 (fun a => a).        (* 720 *)


Lemma fact_Sn :
  forall n,
    fact (S n) = (S n) * fact n.
Proof.
Admitted.


Lemma fact_cps_Sn :
  forall n f,
    fact_cps (S n) f =
    fact_cps n (fun (r:nat) => (f (S n * r))).
Proof.
Admitted.

Eval cbv in fact_cps 6 (fun (r:nat) => r).  (* 720 *)
Eval cbv in fact_cps 5 (fun (r:nat) => (6 * r)). (* 720 *)

Lemma eq_fact_fact_cps_aux :
  forall (n:nat),
    (forall f, f (fact n) = fact_cps n f) /\
    (forall g, g (fact (S n)) = fact_cps (S n) g).
Proof.
Admitted.

Theorem eq_fact_fact_cps :
  forall n f, f (fact n) = fact_cps n f.
Proof.
Admitted.

End Question.

(**
# 回答

こちらが、Admittedを解消して、完全な証明にしたコードです。
また、Module名もQuestionからAnserに変更しました。
*)
Module Anser.

Fixpoint fact (n : nat) : nat :=
  match n with
    | 0 => 1
    | (S n') => n * fact n'
  end.
Eval cbv in fact 6.                         (* 720 *)

Fixpoint fact_cps (n : nat) (cont : nat -> nat) : nat :=
  match n with
    | 0 => cont 1
    | (S n') => fact_cps n' (fun (a : nat) => cont (n * a))
  end.
Eval cbv in fact_cps 6 (fun a => a).        (* 720 *)

Lemma fact_Sn :
  forall n,
    fact (S n) = (S n) * fact n.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma fact_cps_Sn :
  forall n f,
    fact_cps (S n) f =
    fact_cps n (fun (r:nat) => (f (S n * r))).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Eval cbv in fact_cps 6 (fun (r:nat) => r).  (* 720 *)
Eval cbv in fact_cps 5 (fun (r:nat) => (6 * r)). (* 720 *)

Lemma eq_fact_fact_cps_aux :
  forall (n:nat),
    (forall f, f (fact n) = fact_cps n f) /\
    (forall g, g (fact (S n)) = fact_cps (S n) g).
Proof.
  intros.
  induction n.
  - split.
    + intros f.
      simpl.
      reflexivity.
    + intros g.
      simpl.
      reflexivity.
  - destruct IHn as [IHn_fact IHn_Sn].
    split.
    + intros f.
(*    simpl.                                   削除 *)
(*    rewrite IHn_fact.                        削除 *)
      rewrite fact_cps_Sn.
      rewrite <- IHn_fact.                  (* 追加 *)
      reflexivity.
    + intros g.
(*    simpl.                                   削除 *)
(*    rewrite IHn_Sn.                          削除 *)
      rewrite fact_Sn.
      rewrite fact_cps_Sn.
      rewrite <- IHn_Sn.                    (* 追加 *)
      reflexivity.
Qed.

Theorem eq_fact_fact_cps :
  forall n f, f (fact n) = fact_cps n f.
Proof.
  intros.
  apply (proj1 (eq_fact_fact_cps_aux n)).
Qed.

End Anser.

(**
このコードでは、定理証明支援系CoqのCoqIDEなどで実行できます。
それぞれのLemmaとTheoremの証明は、intros、simpl、reflexivityを使用しています。
*)

(* END *)
