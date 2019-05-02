(**
濃度に値の存在の補題について (Proof Pearl ##2)
======
2019/05/01

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_ex_card.v

 *)

(**
# 説明

集合の濃度（有限集合なので、元の個数そのもの）は、決まります。
それ自体は自明なのですが、Mathcomp で証明しようとすると、
どこから手をつけていいか解りません。

Mathcomp の場合、集合は有限型(finType)をドメインとするbooleanな関数で
表されます。すなわち、

``T : finType`` のとき、 ``p : pred T``


なお、``pred T` は単に ``T -> bool`` の表記です。

集合pと関数pが同一視され、集合pの濃度は、型Tの要素の全体を関数pでフィルタリングして
残った要素の数になります。このことから、
型Tの要素の全体をしめす enum すなわち seq に対する帰納法で解くことかできます。


型 T からそのenum を取り出すのは、次のようにします。

``Finite.enum T``

あとは、seq に対する証明と同じです。
ほとんど自明であるがゆえに、
Mathcompにおける実装の裏側を知らないと解けない問題の例といえるでしょう。
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
      case H : (x \in p) => /=.
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
