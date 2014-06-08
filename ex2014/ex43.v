(**
# 第9回 タクティックの定義と利用/停止性証明 (2014/06/08)

http://qnighy.github.io/coqex2014/

## 課題43 (種別:B / 締め切り : 2014/06/22)

ゴールがandの連なった形であるとき、これをandの形になっている限りsplitし続けるタクティックを
定義せよ。課題41と違い、and以外の形の場合はsplitしてはいけない。

*)

Ltac split_all :=
  match goal with
    | _ : _ |- _ /\ _
      => split; split_all
    | _ => idtac
  end.

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
  split.
  - assumption.
  - assumption.
Qed.

(*
ヒント

match goal with ... end 構文を使いましょう。この構文の使い方についてはマニュアルの9章の文法
定義を追うのがよいかと思います。*)

(* END *)
