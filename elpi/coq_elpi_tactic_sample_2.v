(**
Coq-Elpi によるタクティクの作成（その2）
=====================

@suharahiromichi

2023/01/01
*)

(**
定理証明系Coqには、Embeddable Lambda Prolog Interpreter (ELPI) によってタクティク（証明戦略）を
作成するためのパッケージ ``Coq-Elpi``が用意されています。

(その1)[1]で説明しなかった、いくつかのトピックスについて説明します。参考文献は[1]を参照してください。

この記事のソースコードは以下にあります。

https://github.com/suharahiromichi/coq/tree/master/elpi/coq_elpi_tactic_sample_2.v
*)

From elpi Require Import elpi.

(**
# 証明エンジン　(``coq.ltac.collect-goals``)

[1]では、solveの第1引数の``goal Ctx Trigger Type Proof Args``の
Triggerに値を代入することで証明が進み、そここにHole(``_``)があると、
それが新たな（サブ）ゴールになると説明しました。

これはCoqの証明エンジンの機能ですが、それを明示的に呼び出して
処理をおこなうのは、組込述語``coq.ltac.collect-goals``です(注1)。
[2]では、Triggerへの代入と、これの呼び出しをまとめて``refine``として定義されています。
（変数名を変更しました。）

```
pred refine i:term, i:goal, o:list sealed-goal.
refine T (goal _ Trigger _ Proof _) GL :-
  Trigger = T, coq.ltac.collect-goals Proof GL _.
```

(注1) 
- ``coq.ltac.collect-goals``　は、``src/coq_elpi_builtins.ml``
- ``refine`` は。``src/elpi/elpi-ltac.elpi``


以下では、Triggerへの代入はおこなわず、組込述語``refine``を使うようにします。

なお、Elpiのタクティクに引数を渡す箇所(``[trm S]``)は、後述します。
*)
Elpi Tactic refine0.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger Type Proof [trm S] as G) GL :-
    Trigger = S,
    coq.ltac.collect-goals Proof GL _,
    coq.say "goal : " G,
    coq.say "new goal : " GL.
  solve (goal _ _ _ _ [trm S] as G) GL :-
    Msg is {coq.term->string S} ^ " cannot refine",
    coq.ltac.fail _ Msg.
}}.
Elpi Typecheck.

Lemma test_refine0 : forall (P Q : Prop), P -> (P -> Q) -> Q.
Proof.
  intros P Q HP HPQ.
  elpi refine0 (HPQ _).
  elpi refine0 (HP).
Qed.

(**
# エラボレーション (``coq.elaborate-skeleton``)

Holeが埋められるかを事前にチェックしてから、Triggerに
セットします（実際に、穴を埋めるわけではない）。
*)
Elpi Tactic refine1.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger Type Proof [trm S] as G) GL :-
    coq.elaborate-skeleton S Ty T ok, !,
    coq.say "coq.elaborate-skeleton",
    coq.say "S  = " {coq.term->string S},
    coq.say "Ty = " {coq.term->string Ty},
    coq.say "T  = " {coq.term->string T},
    refine T G GL.    % Trigger = T.
  solve (goal _ _ _ _ [trm S]) _ :-
    Msg is {coq.term->string S} ^ " does not fit",
    coq.ltac.fail _ Msg.
}}.
Elpi Typecheck.

Lemma test_refine1 : forall (P Q : Prop), P -> (P -> Q) -> Q.
Proof.
  intros P Q HP HPQ.
  Fail elpi refine1 (HPQ).
  elpi refine1 (HPQ _).
  elpi refine1 (HP).
Qed.

(**
# α等価からの拡張 (``coq.unify-leq``)

``refine``は、λ式におけるα等価（束縛変数の名前の違いをのぞいて同じ）
である場合だけ同じ項と判断します。
この制限を緩和して、ゴールが``id Q`` のとき、これを ``Q``とみなして証明できるようにします。

``coq.unify-leq Ty' Ty`` は、cumulativityに``Ty' ≦ Ty``であることを
チェックするだけなので、値がきまっていないといけません。

そこで、``std.mem``が、バックトラックで、Ctxから取り出す、``Ty'``の値を使い、
``coq.unify-leq {{Q}} {{id Q}}`` すなわち``{{Q}} ≦ {{id Q}}``
から、``Ty' = Q``、``H = HQ``を見つけ出し、
結果として、``Trigger = {{HQ}}``を実行できることになります。
*)

Elpi Tactic assumption2.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger Ty Proof [] as G) GL :-
    std.mem Ctx (decl H _ Ty'),
    coq.unify-leq Ty' Ty ok,
    % ↑これを ``Ty' = Ty`` にると、うまくいかない。
    coq.say "coq.unify-leq",
    coq.say "Ty'= " {coq.term->string Ty'},
    coq.say "Ty = " {coq.term->string Ty},
    coq.say "H  = " {coq.term->string H},
    refine H G GL.    % Trigger = H.
  solve _ _ :-
    coq.ltac.fail _ "no such hypothesis".
}}.
Elpi Typecheck.

Lemma test_assumption2 : forall (P Q : Prop), P -> Q -> P /\ (id Q).
Proof.
  intros P Q HP HQ.
  split.
  - elpi assumption2.
  - elpi assumption2.
Qed.

(**
# タクティクのエラー (``coq.ltac.fail``)

Elpiで書いたタクティクが、Elpiとしして
「失敗」した場合は、以下のfatalエラーになります。
"The elpi tactic/command XXXXX failed without giving a specific error message.
Please report this inconvenience to the authors of the program."

Coqのタクティカルの``repeat``は、タクティクが「実行できる限り実行する」ものですから、
途中で、このようなfatalエラーが発生することは、避けなければなりません。

そこで、Elpiで書いたタクティクのエラーでタクティクを終了する場合は、
組込述語``coq.ltac.fail``を呼び出して、Elpiのコード自体は「成功」させるようにします
（``coq.ltac.fail``自体は、呼び出されると、Elpiとしては「成功」します）。

``coq.ltac.fail``が発生するエラーは、``repeat``がキャッチできるので、
``repeat``の中で使うなら、``repeat``が正常に終了し、
``repeat``の外で使うなら、failして引数のエラーメッセージが表示される。
という動きになります。
*)

Elpi Tactic split.        (* split_ll_bis *)
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger {{ _ /\ _ }} Proof Args as G) GL :-
    refine {{ conj _ _ }} G GL.
  solve _ _ :-  % この節を外すと ``repat elpi split`` が動かない。
   coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

(**
[1]で定義したsplitは、これを守っているため、repeatの中で意図通りに動きます。
*)
Lemma test22 : forall (P1 P2 P3 P4 P5 : Prop),
  P1 -> P2 -> P3 -> P4 -> P5 -> P1 /\ P2 /\ P3 /\ P4 /\ P5.
Proof.
  intros P1 P2 P3 P4 P5 HP1 HP2 HP3 HP4 HP5.

  (* Goal : P1 /\ P2 /\ P3 /\ P4 /\ P5 *)  
  repeat elpi split.
  (* repeat の中から呼び出すと、可能な限りsplitを繰り返し、エラーにならない。 *)

  Undo 1.
  (* Goal : P1 /\ P2 /\ P3 /\ P4 /\ P5 *)  
  elpi split.
  (* Goal : P1 *)
    Fail elpi split.     (* Tactic failure: not a conjunction. *)
    assumption.
    elpi split.
      assumption.
      elpi split.
        assumption.
        elpi split.
        assumption.
        assumption.
Qed.

(**
# 引数の授受

タクティクの引数は solveの第1引数の``goal Ctx Trigger Type Proof Args``のArgsに渡されます。
Args の型は``list argument``で、
さらに、argumentは、[2]の``elpi/coq-HOAS.elpi``で、次のように定義されています。

```
kind argument type.
type int       int    -> argument.
type str       string -> argument.
type trm       term   -> argument.
```
*)

(**
## 引数の受け取り

Elpiの項として必要なのは、int型、string型、term型ですから、Elpiから使うためには、
コンストラクタ``int``、``str``、``trm``は取り去らないといけません。
*)

Elpi Tactic print_arg_int_string_term.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ [int A1, str A2, trm A3]) GL :-
    coq.say A1 ": int",
    coq.say A2 ": string",
    coq.say A3 ": term",
    coq.say {coq.term->string A3} ": term".
  solve _ _ :-
    coq.ltac.fail _ "wrong args".
}}.
Elpi Typecheck.

(**
## 引数の受け渡し

Elpiのコードの中から、他のタクティクを呼び出す場合は、
``coq.ltac.call`` を使います。引数の渡し方は、前節の説明と同じです。

ここではCoqの節``I``を渡していますが、``{{}}``で囲んで書けるので、
以下のように渡すことができます。
*)

Ltac test t := refine t.
Elpi Tactic refine_I.
Elpi Accumulate lp:{{
  solve G GL :-
    coq.ltac.call "test" [trm {{I}}] G GL.
}}.
Elpi Typecheck.

Lemma test_print_args : True.
Proof.
  elpi print_arg_int_string_term 1 x (1 = 0).
  elpi print_arg_int_string_term -1 "x y" (1).
  elpi refine_I.
Qed.

(**
# Coq項の表示 (``coq.term->string``)

Coqの項を渡す場合は、Coq側で``()``で囲む必要があります。

また、Coqの項は、内部表現で表示しても判らないので、
組込述語``coq.term->string``が用意されています。
使用例は前節を参照してください。

述語としては2引数ですが``{}``で囲むことで、関数のように使っています。
``{}``については、[1]の[3]のSpillingの節を参照してください。
*)

(**
# 参考文献

[1] Coq-Elpi によるタクティクの作成（その1の2）

<https://qiita.com/suharahiromichi/items/31096ff47ab69f4ba4ea>


<https://github.com/suharahiromichi/coq/blob/master/elpi/coq_elpi_tactic_sample_1_2.v>



[2] coq-ELPI

<https://github.com/LPCIC/coq-elpi>
*)

(* END *)
