(**
# 第9回 タクティックの定義と利用/停止性証明 (2014/06/08)

http://qnighy.github.io/coqex2014/

## 課題41 (種別:A / 締め切り : 2014/06/15)

splitを試し、成功したら生成された全てのサブゴールで再帰的に
splitを試し続けるタクティックを定義せよ。
*)

Ltac split_all :=
  try (split; split_all); idtac.

(* 以下は動作確認用 *)

Lemma bar :
  forall P Q R S : Prop,
    R -> Q -> P -> S -> (P /\ R) /\ (S /\ Q).
Proof.
  intros P Q R S H0 H1 H2 H3.
  split_all.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma baz :
  forall P Q R S T : Prop,
    R -> Q -> P -> T -> S -> P /\ Q /\ R /\ S /\ T.
Proof.
  intros P Q R S T H0 H1 H2 H3 H4.
  split_all.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma quux :
  forall P Q : Type, P -> Q -> P * Q.
Proof.
  intros P Q H0 H1.
  split_all.
  - assumption.
  - assumption.
Qed.

Record foo := {
  x : (False -> False) /\ True /\ (False -> False);
  y : True;
  z : (False -> False) /\ True
}.

Lemma hogera : foo.
Proof.
  split_all.
  - intros H; exact H.
  - intros H; exact H.
  - intros H; exact H.
Qed.

(**
ヒント

マニュアルの8章はタクティック集、9章はタクティック言語の文法など、
10章は3つの発展的なタクティックの詳細です。これらが一次資料です。

Ltac はタクティックの再帰的定義ができます。
つまり、定義されたタクティックの中で自分自身を呼ぶことができます。
try タクティカルを使いましょう。
*)

(* END *)
