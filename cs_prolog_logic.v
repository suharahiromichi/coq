(**
Prologの証明手順とCoqのautoタクティクについて
======
2016/12/12

@suharahiromichi


# はじめに

論理型言語Prologは、一階述語論理（のサブセット）に対する自動証明をプロ
グラムの実行とみなすプログラミング言語です。なので、Prologのプログラム
を一階述語論理のかたちに戻してやれば、Coqのような定理証明系のうえでも
証明できるはずです。実際、Coq Reference Manual (文献[1]) のautoタクティクの
説明には、

> This tactic implements a Prolog-like resolution procedure to solve the current goal. 


と書いてあります。また、CPDT (文献[2]) の第13章は論理型プログラミングの考え
方をCoqでの証明に応用することが説明されています。ここでは、Prologによ
る定理証明と、Coqのautoおよびeautoタクティクを比較してみます。

PrologもCoqも「おなじだね」と思えるかどうかは、読んだ方の判断にまかせようとおもいます。

この文書のソースコードは、

https://github.com/suharahiromichi/coq/cs_prolog_logic.v

にあります。
*)

(**
# Prologの実行手順

Prologを定理証明器としてみたとき、文法的にホーン節という一階述語論理の
サブセットに限定したうえで、その矛盾を 左側深さ優先 の証明探索で示すものです。
定理でないものを証明してしまうことはないので健全ですが、
ホーン節に限定しても全ての定理を証明できないため完全ではありません。
証明できない定理の例は後で示します。


```Prolog:Prologプログラム1
  s(X, Y).                                   % (1)
  p(X, Y) :- q(X, Y), r(X, Y).               % (2)
  ?- g(X, Y), h(X, Y).                       % goal
```


Prologでは、変数を大文字から、述語を含む定数を小文字から始めます。
これをホーン節にすると、


```:論理式1
  ∀x y,(true → s(x, y))                    (* 確定節（単位節）*)
  ∀x y,(q(x, y) ∧ r(x, y) → p(x, y))      (* 確定節 *)
  ∀z y,(g(x, y) ∧ h(x, y) → false)        (* ゴール節 *)
```


節とは連言標準型の項のことですから、ホーン節のすべてを∧で結びます。
また、全体から矛盾を導くので 「⊢ false」 となります。


```:論理式2
  [∀x y,(true → s(x, y))]               ∧
  [∀x y,(q(x, y) ∧ r(x, y) → p(x, y))] ∧
  [∀z y,(g(x, y) ∧ h(x, y) → false)] ⊢ false
```


この論理式は、「⊢」の両辺を入れ換えたあと、二重否定の除去などの古典論理の公理をつかうと、
次の論理式に変換できます。実際の変換は文献[3]や[4]などを参照してください。


```:論理式3
  ⊢ [∀x y,(s(x, y))]                       →
    [∀x y,(q(x, y) ∧ r(x, y) → p(x, y))] →
    [∃z y,(g(x, y) ∧ h(x, y))]
```


しかし、実際にPrologのプログラムを書く場合に、上記の変換を心に留めているかというと
大いに疑問で、Pologのプログラムが最後の論理式3と等価であると、「直観的」に、
あるいは 直観主義論理 の範疇で認識しているように思います。

今日は、これ以上この問題に踏み込みませんが、
Prologのプログラムと一階述語論理の論理式には、
対応があることを理解してください。

なお、論理式をPrologのプログラムに変換するとき、連言標準型にしたあと
∃を取り除く必要があります。そのために「スコーレム関数」を導入しますが、
それもここでは省略します。
 *)

(**
# リストのメンバーシップ述語の例

次のプログラムを考えます。リストのメンバーシップ述語を定義したうえで、
「リスト [1, 2, 3] に含まれる、1より大きいな要素」を求めようとしています。
もちろん X = 2 という答えが得られます。
さらに代替解として X = 3 も得られますが、
今日は最初の解が得られるまでを問題にしたいとおもいます。

Prologでは、リストは [1, 2, 3]、AとDのconsは [A | D] で示します。


```Prolog:Prologプログラム2
  member(X, [X | _]).
  member(X, [_ | L]) :- member(X, L).
  ?- member(X, [1, 2, 3]), X > 1.
```

X=2が得られるまでの実行をトレースしてみましょう。

```
  ?- spy(member).
  true.
  
  [debug]  ?- member(X, [1,2,3]),  X > 1.
   * Call: (8) member(_G339, [1, 2, 3]) ? creep
   * Exit: (8) member(1, [1, 2, 3]) ? creep
     Call: (8) 1>1 ? creep
     Fail: (8) 1>1 ? creep
   * Redo: (8) member(_G339, [1, 2, 3]) ? creep
   * Call: (9) member(_G339, [2, 3]) ? creep
   * Exit: (9) member(2, [2, 3]) ? creep
   * Exit: (8) member(2, [1, 2, 3]) ? creep
     Call: (8) 2>1 ? creep
     Exit: (8) 2>1 ? creep
  X = 2 .
```

```
         member(X, [1, 2, 3]), X > 1
           ／              ＼
  member(1, [1 | _])      member(X, [_ | [2, 3]) :- member(X, [2, 3])
          |                         |
         1 > 1            member(X, [2, 3])
          |                         |
         FAIL             member(2, [2 |_])
                                    |                  
                                  2 > 1
                                    |
                                  (成功)
```

``member(X, [1, 2, 3])`` に対して、``member(X, [X | _])`` を選ぶことで、
``X=1`` を得る。 ``1 > 1`` が成立せず失敗する。

``member(X, [1, 2, 3])`` に対して、``member(X, [_ | L) :- member(X, L)`` ついで、
``member(X, [X | _])`` を選ぶことで、``X=2`` を得る。 ``2 > 1`` が成立して成功する。
 *)

(**
# Coq での証明


Coq (Mathcomp) では、述語の引数は(OCamlのように)括弧を省略します。
また、リストは [:: 1, 2, 3]、AとDのconsは A :: D で示します。

Inductive から始まる定義で、member述語の型を定義します。Lemma が実際の証明です。
まず「move=> H1 H2」を実行することで、
確定節にあたる部分を前提に、ゴール節にあたる部分をゴールにしています。

そして、eauto が自動証明にあたります。
eauto は、ゴールに対して前提を apply と eapply することで証明を試みます。
eapply は、applyのとき、未定の変数を未定のまま証明を進めることができるものです。
ただし、どこかで値が決まらなければなりません。

eauto の引数の4は、自動証明の深さの制限をします。
この場合は、4より少ない値だと証明できません。
debug はなくてもよく、ここではeautoの自動証明をトレースします。

その結果として、No more subgoals. と表示されて、証明が完了したことを示します。

Show Proof で、証明の根拠（エビデンス）となる関数項が表示されます。
それをよくよくみると、任意のX (∃ X) に対して、2 が選ばれていることがわかります。
（わかるかな？？？？ ex_intro の第二引数の「2」がそれです。）
 *)

From mathcomp Require Import all_ssreflect.

Inductive member : nat -> seq nat -> Prop :=
| Mem : forall x l, member x l.

Lemma mem1 : (forall x l, member x (x :: l)) ->
             (forall x y l, member x l -> member x (y :: l)) ->
             (exists x, member x [:: 1; 2; 3] /\ x > 1).
Proof.
  move=> H1 H2.
  (*
  H1 : forall (x : nat) (l : seq nat), member x (x :: l)
  H2 : forall (x y : nat) (l : seq nat), member x l -> member x (y :: l)
  ============================
   exists x : nat, member x [:: 1; 2; 3] /\ 1 < x
   *)

  debug eauto 4.
  (*
  Debug: (* debug eauto : *)
  Debug: 1 depth=4
  Debug: 1.1 depth=3 eapply ex_intro
  Debug: 1.1.1 depth=2 apply conj
  -------------------------------------------------------------
  Debug: 1.1.1.1 depth=2 apply H1                         ^
  Debug: 1.1.1.1.1 depth=1 apply prime_gt1                |
  Debug: 1.1.1.1.1.1 depth=0 unfold is_true               |
  Debug: 1.1.1.1.2 depth=1 apply ltnW                     |
  Debug: 1.1.1.1.2.1 depth=0 apply ltnW                   |back
  Debug: 1.1.1.1.2.2 depth=0 unfold is_true               |track
  Debug: 1.1.1.1.3 depth=1 unfold is_true                 |
  Debug: 1.1.1.1.3.1 depth=0 apply Bool.absurd_eq_true    |
  Debug: 1.1.1.1.3.2 depth=0 eapply Bool.trans_eq_bool    v
  -------------------------------------------------------------
  Debug: 1.1.1.2 depth=1 apply H2
  Debug: 1.1.1.2.1 depth=1 apply H1
  Debug: 1.1.1.2.1.1 depth=1 apply leqnn
   *)

  Show Proof.
  (*
  (fun (H1 : forall (x : nat) (l : seq nat), member x (x :: l))
     (H2 : forall (x y : nat) (l : seq nat), member x l -> member x (y :: l)) =>
   ex_intro (fun x : nat => member x [:: 1; 2; 3] /\ 1 < x) 2
     (conj (H2 2 1 [:: 2; 3] (H1 2 [:: 3])) (leqnn 2)))
   *)

  Undo 1.
  eapply ex_intro.
  split.
  - apply H2.
    apply H1.
  - exact.                                  (* 1 < 2 *)
Qed.


(**
```
         ∃x,(member(X, [1, 2, 3]), X > 1
                           |
                   eapply ex_intro
                   member(?, [:: 1, 2, 3])
           ／                                  ＼
       apply H1                              apply H2
       member(1, 1 :: [:: 2, 3])             member(?, [:: 2, 3]) -> member(?, 1 :: [:: 2, 3])
          |                                  member(?, [:: 2, 3])
          |                                     |
         1 < 1                               apply H1
          |                                  member(2, 2 :: [:: 3])
          |                                     |
         Fail                                  1 < 2
                                                |
                                               exact.
```

最初の apply H1 で、メタ変数 ``?`` は 1 になります。
メタ変数への束縛もバックトラックで解除されるので、2回めの apply H1 で、
メタ変数 ``?`` は 2 になります。

exists x : nat の x が自然数であることのの情報を使って、
x = 0,1,2,3... とチェックしているのでは *ない* ことに注意してください。

Prologの証明手続きと同じだということが解るでしょうか。
*)

(**
# Prologでは証明できない例


```Prolog:Prologプログラム3
  p(a, b).                            % (1)
  p(c, b).                            % (2)
  p(X, Z) :- p(X, Y), p(Y, Z).        % (3)
  p(X, Y) :- p(Y, X).                 % (4)
  
  ?- p(a, c).                         % goal
```

実行をトレースすると次のようになります。
途中で得られた p(b, Z) を 節(3)で永久に展開しつづけて、
スタックがあふれてエラーになりますので、途中でアボートしています。

```
  ?- spy(p).
  true.
  
  [debug]  ?- p(a, c).
   * Call: (7) p(a, c) ? creep
   * Call: (8) p(a, _G392) ? creep
   * Exit: (8) p(a, b) ? creep
   * Call: (8) p(b, c) ? creep
   * Call: (9) p(b, _G392) ? creep
   * Call: (10) p(b, _G392) ? creep
   * Call: (11) p(b, _G392) ? creep
   * Call: (12) p(b, _G392) ? creep
   * Call: (13) p(b, _G392) ? creep
   * Call: (14) p(b, _G392) ? creep
   * Call: (15) p(b, _G392) ? creep
   * Call: (16) p(b, _G392) ? abort
  % Execution Aborted
```



これは、 applyする前提を適当に選ぶと以下のような証明木が作れます。
最良の選び方をしているので、バックトラックがまったく発生していないことに注意してください。

```
  p(a, c)
     |
    (3)
     |
  p(a, c) :- p(a, Y), p(Y, c)
  p(a, Y), p(Y, c)
     |
     |
  p(a, Y),  p(Y, c)
     |         |
    (1)        |
     |         |
  p(a, b),  p(Y, c)
  true         |
            p(Y, c)
               |
              (4)
               |
            p(Y, c) :- p(c, Y)
            p(c, Y)
               |
              (2)
               |
            p(c, b)
            true

```

 *)

Module sampl1.

Inductive data : Set := a | b | c.

Inductive p : data -> data -> Prop :=
| P : forall x y, p x y.

Goal (p a b) ->
     (p c b) ->
     (forall x y z, p z y /\ p y z -> p x z) ->
     (forall x y, p x y -> p y x) ->
     (p a c).
Proof.
  move=> H1 H2 H3 H4.
  (*
  H1 : p a b
  H2 : p c b
  H3 : forall x y z : data, p z y /\ p y z -> p x z
  H4 : forall x y : data, p x y -> p y x
  ============================
   p a c
   *)
  
  debug eauto 5.
  (*
  Debug: (* debug eauto : *)
  Debug: 1 depth=5
  Debug: 1.1 depth=4 apply H4
  -------------------------------------------------------------
  Debug: 1.1.1 depth=3 apply H4                           ^    
  Debug: 1.1.1.1 depth=2 apply H4                         |    
  Debug: 1.1.1.1.1 depth=1 apply H4                       |    
  Debug: 1.1.1.1.1.1 depth=0 apply H4                     |    
  Debug: 1.1.1.1.1.2 depth=0 eapply H3                    |
  Debug: 1.1.1.1.2 depth=1 eapply H3                      |
  Debug: 1.1.1.1.2.1 depth=0 apply conj                   |back    
  Debug: 1.1.1.2 depth=2 eapply H3                        |track    
  Debug: 1.1.1.2.1 depth=1 apply conj                     |    
  Debug: 1.1.1.2.1.1 depth=1 exact H2                     |
  Debug: 1.1.1.2.1.1.1 depth=0 apply H4                   |
  Debug: 1.1.1.2.1.1.2 depth=0 eapply H3                  |
  Debug: 1.1.1.2.1.2 depth=0 apply H4                     |
  Debug: 1.1.1.2.1.3 depth=0 eapply H3                    v
  -------------------------------------------------------------
  Debug: 1.1.2 depth=3 eapply H3
  Debug: 1.1.2.1 depth=2 apply conj
  Debug: 1.1.2.1.1 depth=2 exact H1
  Debug: 1.1.2.1.1.1 depth=1 apply H4
  Debug: 1.1.2.1.1.1.1 depth=1 exact H1
   *)
  
  Undo 1.
  apply (H4 c a).
  eapply (H3 c _ a).
  split.
  - apply H1.
  - apply H4.
    apply H1.

  Undo 8.
  eapply (H3 a _ c).
  split.
  - apply H2.
  - apply (H4 c b).
    apply H2.
Qed.
End sampl1.

(**
```
     p(a, c)
        |
  apply (H3 a _ c)
  p(a, Y),             p(Y, c)
     |                    |
  apply (H1)              |
  p(a, b),             p(Y, c)
  true                    |
                       p(Y, c)
                          |
                       apply H4
                       p(c, Y)
                          |
                       apply H2
                       p(c, b)
                       true

```

 *)

(**
# Prologでは証明できない例 (その2)

```Prolog:Prologプログラム4
  p(X, Z) :- p(Y, Z), q(X, Y).                /* (1) */
  p(X, X).                                    /* (2) */
  q(a, b).                                    /* (3) */
  ?- p(X, b)                                  /* goal */
```

これは、ゴールに対して、最初の節である (1) が適用されたあと、
(1)の再帰呼び出しが終了しないため、スタックオーバーフローで停まります。
ゴールに対して、最初に(1)ではなく(2)を適用すると、問題なく解が得られます。
 *)

Module sampl2.
Inductive data : Set := a | b.

Inductive q : data -> data -> Prop :=
| Q : forall x y, q x y.

Inductive p : data -> data -> Prop :=
| P : forall x y, p x y.

Goal (forall x y z, p y z /\ q x y -> p x z) ->
     (forall x, p x x) ->
     (q a b) ->
     (exists x, p x b).
Proof.
  move=> H1 H2 H3.
  (*
  H1 : forall x y z : data, p y z /\ q x y -> p x z
  H2 : forall x : data, p x x
  H3 : q a b
  ============================
   exists x : data, p x b
   *)
  
  debug eauto 5.
  (*
  Debug: (* debug eauto : *)
  Debug: 1 depth=5
  Debug: 1.1 depth=4 eapply ex_intro
  Debug: 1.1.1 depth=4 apply H2
   *)
  Show Proof.
  (*
  (fun (_ : forall x y z : data, p y z /\ q x y -> p x z)
     (H2 : forall x : data, p x x) (_ : q a b) => ex_intro (p^~ b) b (H2 b))
   *)
  
  Undo 1.
  exists b.
  apply H2.
Qed.
End sampl2.
  
(**
# ふたたびメンバーシップ述語の例
Prologの場合は、最初に X = 3 が得られる。

```:Prolog:プログラム5
  member(X, [_ | L]) :- member(X, L).
  member(X, [X | _]).
  ?- member(X, [1, 2, 3]), X > 1.
```

Coqの場合は、結果は変わらないが、ずいぶんと遠回りする。
 *)

Lemma mem2 : (forall x y l, member x l -> member x (y :: l)) ->
             (forall x l, member x (x :: l)) ->
             (exists x, member x [:: 1; 2; 3] /\ x > 1).
Proof.
  move=> H1 H2.
(*
  Debug: (* debug eauto : *)
  Debug: 1 depth=5
  Debug: 1.1 depth=4 eapply ex_intro
  Debug: 1.1.1 depth=3 apply conj
  -------------------------------------------------------------
  Debug: 1.1.1.1 depth=3 apply H2                            ^
  Debug: 1.1.1.1.1 depth=2 apply prime_gt1                   |
  Debug: 1.1.1.1.1.1 depth=1 unfold is_true                  |
  Debug: 1.1.1.1.1.1.1 depth=0 apply Bool.absurd_eq_true     |
  Debug: 1.1.1.1.1.1.2 depth=0 eapply Bool.trans_eq_bool     |
  Debug: 1.1.1.1.2 depth=2 apply ltnW                        |
  Debug: 1.1.1.1.2.1 depth=1 apply ltnW                      |
  Debug: 1.1.1.1.2.1.1 depth=0 apply ltnW                    |
  Debug: 1.1.1.1.2.1.2 depth=0 unfold is_true                |
  Debug: 1.1.1.1.2.2 depth=1 unfold is_true                  |
  Debug: 1.1.1.1.2.2.1 depth=0 apply Bool.absurd_eq_true     |
  Debug: 1.1.1.1.2.2.2 depth=0 eapply Bool.trans_eq_bool     |back
  Debug: 1.1.1.1.3 depth=2 unfold is_true                    |track
  Debug: 1.1.1.1.3.1 depth=1 apply Bool.absurd_eq_true       |
  Debug: 1.1.1.1.3.1.1 depth=0 apply not_false_is_true       |
  Debug: 1.1.1.1.3.2 depth=1 eapply Bool.trans_eq_bool       |
  Debug: 1.1.1.1.3.2.1 depth=1 apply erefl                   |
  Debug: 1.1.1.1.3.2.1.1 depth=0 apply Bool.absurd_eq_true   |
  Debug: 1.1.1.1.3.2.1.2 depth=0 eapply Bool.trans_eq_bool   |
  Debug: 1.1.1.1.3.2.2 depth=1 apply Logic.eq_sym ; trivial  |
  Debug: 1.1.1.1.3.2.2.1 depth=0 apply Bool.absurd_eq_true   |
  Debug: 1.1.1.1.3.2.2.2 depth=0 eapply Bool.trans_eq_bool   |
  Debug: 1.1.1.1.3.2.3 depth=0 apply Bool.absurd_eq_true     |
  Debug: 1.1.1.1.3.2.4 depth=0 apply f_equal_nat             |
  Debug: 1.1.1.1.3.2.5 depth=0 apply f_equal2_nat            |
  Debug: 1.1.1.1.3.2.6 depth=0 eapply Bool.trans_eq_bool     v
  -------------------------------------------------------------
  Debug: 1.1.1.2 depth=2 apply H1
  Debug: 1.1.1.2.1 depth=2 apply H2
  Debug: 1.1.1.2.1.1 depth=2 apply leqnn
*)
  debug eauto 5.
  Show Proof.
(*
  (fun (H1 : forall (x y : nat) (l : seq nat), member x l -> member x (y :: l))
     (H2 : forall (x : nat) (l : seq nat), member x (x :: l)) =>
   ex_intro (fun x : nat => member x [:: 1; 2; 3] /\ 1 < x) 2
     (conj (H1 2 1 [:: 2; 3] (H2 2 [:: 3])) (leqnn 2)))
*)
Qed.

(**
# まとめ

Prologの証明手順と、Coqのautoタクティク(eautoタクティク)を比べてみました。
どちらも、左側深さ優先の証明探索をする意味でおなじ結果になります。
ただし、Prologがスタックがあふれるまで深く探索するのに対して、
autoやeautoタクティクは指定された深さで打ちきるので、結果として、
より公平は証明探索になり、証明できる範囲は広いといえそうです。
ただし、深さの指定によっては証明できない場合があります。

また、autoやeautoタクティクは
Prologのように前提の順番ではなく、
その形で（Q -> P よりも 「->」のない S のほうを優先して）適用するので、
このことでも、無限の深さへの探索に陥り難くしています。

しかし、auto、eauto とも、ここで述べた以上の賢いヒューリスティックスを備えてはいないようです。


補足するべきこと：

- 深さの定義、数え方。
- Prologで証明できない定理に、無限バックトラックの例を追加する。
*)

(**
# 参考文献

1. "The Coq Proof Assistant Reference Manual" https://coq.inria.fr/refman/
2. Adam Chlipala "Certified Programming with Dependent Types" http://adam.chlipala.net/cpdt/
3. J.W.ロイド、佐藤 他訳「論理プログラミングの基礎」産業図書
4. R.コワルスキ、浦 監訳「論理による問題の解決」培風館
*)

(* END *)
