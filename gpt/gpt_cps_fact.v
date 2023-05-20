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

「

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
Eval cbv in fact 6.

Fixpoint fact_cps (n : nat) (cont : nat -> nat) : nat :=
  match n with
    | 0 => cont 1
    | (S n') => fact_cps n' (fun (a : nat) => cont (n * a))
  end.
Eval cbv in fact_cps 6 (fun a => a).


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

Eval cbv in fact_cps 6 (fun (r:nat) => r).
Eval cbv in fact_cps 5 (fun (r:nat) => (6 * r)).

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
」
*)

(**
# 回答

「

こちらが、Admittedを解消して、完全な証明にしたコードです。
また、Module名もQuestionからAnserに変更しました。
*)
Module Anser.

Fixpoint fact (n : nat) : nat :=
  match n with
    | 0 => 1
    | (S n') => n * fact n'
  end.
Eval cbv in fact 6.

Fixpoint fact_cps (n : nat) (cont : nat -> nat) : nat :=
  match n with
    | 0 => cont 1
    | (S n') => fact_cps n' (fun (a : nat) => cont (n * a))
  end.
Eval cbv in fact_cps 6 (fun a => a).

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

Eval cbv in fact_cps 6 (fun (r:nat) => r).
Eval cbv in fact_cps 5 (fun (r:nat) => (6 * r)).

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

」
 *)

(**
# 補足説明

結果に再現性はないようです。なので、あくまでも一例（とくに良かった場合ではない）と理解してください。

感覚的にですが、繰り返す毎に悪くなるような気もします（NEW CHATを選んだ場合でも）。

質問のもとになったCoqのコードは、GitHubで公開されれいます(2010年公開)が、
回答は、それを書き写したといえるものではありません。

``https://github.com/suharahiromichi/coq/blob/master/coq_cps_fact.v``

もっとも、同様の定理の証明は多くのひとが行い、公開しているはずなので、
それらのどれかを参考にしているかのしれません。
ChatGPTの「Coq力」を測るには、より多くのオリジナルな定理の証明をやらせてみる必要があるでしょう。


最後に、これも感覚的にですが、MathCompよりもStandard Coqの場合のほうが、
まともなコードを返すことが多いようです。

*)

(* END *)
