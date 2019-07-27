(**
有限集合の濃度の存在を証明する
======
2019/05/01

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_ex_card.v

 *)

(**
OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)

(**
# 説明

へんなタイトルですが、Mathcomp を使った定理の証明の問題です。

有限集合の濃度、すなわち要素の個数は、適当な自然数に一意的に決まります。
濃度を ``#| _ |`` で表すとすると、

``∃ i : nat, #| p | = i``


ですね。これ自体は自明なのですが、Mathcomp で証明しようとすると、
取り付く島もないように見えます。

でも、すこし考えてみると、
Mathcomp の場合、集合は有限型(finType)をドメインとするbooleanな関数で
表されます。すなわち、

``T : finType`` のとき、 ``p : pred T``


なお、``pred T` は単に ``T -> bool`` の表記です。

集合pと関数pが同一視されるので、集合pの濃度は、
「型Tの要素の全体を関数pでフィルタリングして残った要素の数」
になります。

このことから、
型Tの要素の全体をしめす finType の enum フィールドの中身、
すなわち seq に対する帰納法で解くことかできることがわかります。


型 T からその enum フィールドの中身を取り出すのは、次のようにします。

``Finite.enum T``

あとは、seq に対する証明と同じです。
ほとんど自明であるがゆえに、
Mathcompにおける実装の裏側を知らないと解けない問題の例といえるでしょうか。
 *)

(**
# コード例
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Test.
  
  Variable T : finType.
  Variable p : pred T.                      (* T -> bool *)

  Lemma ex_card : exists i, #| p | = i.
  Proof.
    rewrite unlock /card /enum_mem /=.
    elim: (Finite.enum T).
    - by exists 0.
    - move=> x s /= [i IHs].
      case: ifP => /=.
      + exists i.+1.
          by rewrite IHs.
      + by exists i.
  Qed.

End Test.

(**
# 最初に使った箇所

単一化の証明 http://fetburner.hatenablog.com/entry/2015/12/06/224619

Unify.v を Mathcomp への移植するときに必要になりました。移植例：

https://github.com/suharahiromichi/coq/blob/master/unify/ssr_unify_bool_3.v
*)

(* END *)
