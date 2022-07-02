(**
Pascalの三角形とルール60の基本セルオートマトン

2022_07_03 @suharahiromichi


# はじめに

Pascalの三角形の奇数だけを塗り潰したものとElementary Cellular Automaton (ECA 文献[1]) の
rule 60 が一致することを証明します。

有名なシェルピンスキーのガスケットは、ECAのrule 90なので、同じではありません（文献[2]）。
*)

From mathcomp Require Import all_ssreflect.
Require Import Recdef.                      (* Function コマンド *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# Elementary Cellular Automaton

ECAは、上の行の左側の列、同列、左側の列の三つのセルだけから 0/1 (= 死/
性) が決まるセルオートマトンです。ルールは、左同右をXYZで表したとき、
その関数で定義されます。例えばルール60の定義は以下の通りです。

```
      XYZ XYZ XYZ XYZ XYZ XYZ XYZ XYZ
引数: 111 110 101 100 011 010 001 000
結果   0   0   1   1   1   1   0   0
```

``00111100`` を2進数で読むと60になるので、ルール60と呼ばれるわけです。
このルールをよく見ると、Zは結果に影響せず、XとYの排他的論理和 EXOR
になっていることがわかります。

ssrbool.v で、排他的論理和は``addb``関数、演算子は``(+)``で定義されているので、
下記の通り定義できます。
*)
Definition rule60 (x y z : bool) := x (+) y.
Definition rule90 (x y z : bool) := x (+) z.

(**
ECA は定義を書き下すだけですが、Coqに帰納原理を生成するために Function
コマンドをつかいます。nを行、kを列とします。
*)
Function eca rule (n k : nat) : bool :=
  match n, k with
  | _, 0 => true (* (0,0) だけがtrueであるべきで、ECAの一般性がない？ *)
  | 0, k'.+1 => false
  | n'.+1, k'.+1 =>
      rule (eca rule n' k') (eca rule n' k) (eca rule n' k.+1)
  end.

(**
# 定理の証明

Pascalの三角形はMathCompのbinomialを使って書きます。
また。functional induction で、Coqの生成した eca についての帰納原理
*)
Check eca_ind.
(**
をつかうことで、簡単に証明できます。
*)
Lemma binomial_ca60 (rule : bool -> bool -> bool -> bool) n k :
  odd (binomial n k) = eca rule60 n k.
Proof.
  functional induction (eca rule n k) => //=.
  - by elim: n.
  - rewrite binS oddD addbC /rule60.
    by rewrite -IHb -IHb0.
Qed.

(**
# 種明かし

binomial の斬化式による定義は、以下の通りです。
*)
Function binomial' (n k : nat) : nat :=
  match n, k with
  | _, 0 => 1
  | 0, _.+1 => 0
  | n'.+1, k'.+1 => binomial' n' k' + binomial' n' k
  end.
(**
また、rule60 の ECA は、以下であるため、両者が同じなのは自明といえます。
 *)
Fixpoint ca60 (n k : nat) : bool :=
  match n, k with
  | _, 0 => true
  | 0, k'.+1 => false
  | n'.+1, k'.+1 => ca60 n' k (+) ca60 n' k'
  end.

(**
実は、10年前に、この二つの定義だけ書きつけておいてあったものに、
証明をつけてみました。

そのときのメモを転載します。
*)

(*
(ここから)

「パスカルの三角形の奇数のみを塗りつぶすと、シェルピンスキーのギャ
スケットが出現する」と簡単に説明されることがあるが、このガスケットが
cellular automaton rule 90を指すのは、多少無理がある。なぜなら、k番目の
セルは、パスカルの三角形（二項定理）は上の段のk-1とkで決まるのに対して、
rule 90は、k-1とk+1で決まるからである。また、rule 90は左側（負の方向）
にも伸びるので、kを負数に対しても定義しないといけない。rule 60とすると
話しは易しい。
*)

(**
[[
rule 60                          rule 90
   1                                1                     
   1 1                            1 0 1
   1 0 1                        1 0 0 0 1
   1 1 1 1                    1 0 1 0 1 0 1
   1 0 0 0 1                1 0 0 0 0 0 0 0 1
   1 1 0 0 1 1            1 0 1 0 0 0 0 0 1 0 1
   1 0 1 0 1 0 1        1 0 0 0 1 0 0 0 1 0 0 0 1
   1 1 1 1 1 1 1 1    1 0 1 0 1 0 1 0 1 0 1 0 1 0 1
]]
*)

(**
[[
rule 60の定義：
60 = 0x3c = 00111100

111 110 101 100 011 010 001 000
 0   0   1   1   1   1   0   0
最右のセルは無視できるので、それを捨てると自然に二項係数に対応する。
11      10      01      00
 0       1       1       0

rule 90の場合は：
90 = 0x5a = 01011010

111 110 101 100 011 010 001 000
 0   1   0   1   1   0   1   0
真中のセルは無視できるので、それを捨てる。
すると二項定理と対応がつくことになる。
1_1 1_0         0_1 0_0
 0   1           1   0
]]

ew.wikipedia.orgにはちゃんと書いてあって、

The pattern produced by an
elementary cellular automaton using rule 60 is exactly Pascal's
triangle of binomial coefficients reduced modulo 2 （中略）.
Rule 90 produces the same pattern but with an empty cell separating
each entry in the rows.

列の中の各エントリーを空のセルで分離すると、ルール90は同じパターンを生成する。

(ここまで)
*)

(**
引用部分は、英語版のWikipedia （文献[3]）から削除されていて、
なにか問題があったのかもしれない。
*)

(**
# 文献

[1] https://mathworld.wolfram.com/ElementaryCellularAutomaton.html

[2] https://qiita.com/Lirimy/items/9e13b156d53a71e5b72f

[3] Cellular automaton [https://en.wikipedia.org/wiki/Cellular_automaton]
*)

(* END *)
