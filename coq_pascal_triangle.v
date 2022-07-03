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
Definition rule90 (x y z : bool) := x (+) z. (* N.G. *)

(**
ECA は定義を書き下すだけですが、Coqに帰納原理を生成するために Function
コマンドをつかいます。nを行、kを列とします。

注意：このECAの定義は一般性に欠ける。
ここでは、初期値 {1, 0, 0, ....} からはじまり、列は正の方向に伸びていくECAだけを扱う。
すると、XYだけを使うルールだけが有効になる。Zはつねにfalseであるため。
 *)
Function eca rule (n k : nat) : bool :=
  match n, k with
  | 0, 0 => true               (* 初期値は {1,0,0, …} に限定する。 *)
  | 0, _.+1 => false
  | n'.+1, 0 =>
      rule false (eca rule n' 0) false
  | n'.+1, k'.+1 =>
      rule (eca rule n' k') (eca rule n' k) false (* (eca rule n' k.+1) *)
(* 初期値を限定しているので、Z=(eca rule n' k.+1) はつねに false である。 *)
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
  - by rewrite -IHb bin0.
  - rewrite binS oddD addbC /rule60.
    by rewrite -IHb -IHb0.
Qed.

(**
# 種明かし

binomial の斬化式による定義は、以下の通りです。
*)
Function binomial' (n k : nat) : nat :=
  match n, k with
  | 0, 0 => 1
  | 0, _.+1 => 0
  | n'.+1, 0 => binomial' n' 0
  | n'.+1, k'.+1 => binomial' n' k' + binomial' n' k
  end.
(**
また、rule60 の ECA は、以下であるため、両者が同じなのは自明といえます。
 *)
Function eca60 (n k : nat) : bool :=
  match n, k with
  | 0, 0 => true
  | 0, k'.+1 => false
  | n'.+1, 0 => eca60 n' 0
  | n'.+1, k'.+1 => eca60 n' k (+) eca60 n' k'
  end.
Compute eca60 0 0.                          (* true *)
Compute eca60 1 0.                          (* true *)
Compute eca60 1 1.                          (* true *)
Compute eca60 2 0.                          (* true *)
Compute eca60 2 1.                          (* false *)
Compute eca60 2 2.                          (* true *)

Lemma binomial_eca60' n k : odd (binomial' n k) = eca60 n k.
Proof.
  functional induction (eca60 n k) => //=.
  by rewrite oddD addbC IHb IHb0.
Qed.

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
```
Pascalの三角形
   1
   1 1
   1 2 1
   1 3 3 1
   1 4 6 4 1
   1 51010 5 1
   1 6152015 6 1
   1 721353521 7 1

rule 60                          rule 90
   1                                1                     
   1 1                            1 0 1
   1 0 1                        1 0 1 0 1
   1 1 1 1                    1 0 1 0 1 0 1
   1 0 0 0 1                1 0 1 0 1 0 1 0 1
   1 1 0 0 1 1            1 0 1 0 1 0 1 0 1 0 1
   1 0 1 0 1 0 1        1 0 1 0 1 0 1 0 1 0 1 0 1
   1 1 1 1 1 1 1 1    1 0 1 0 1 0 1 0 1 0 1 0 1 0 1
```
*)

(**
- 2項係数の定義：
``nCk = (n - 1)C(k - 1) + (n - 1)Ck``

- rule 60の定義：
``60 = 0x3c = 00111100``

```
XYZ XYZ XYZ XYZ XYZ XYZ XYZ XYZ
111 110 101 100 011 010 001 000
 0   0   1   1   1   1   0   0
XY      XY      XY      XY 
11      10      01      00
 0       1       1       0
```

最右のセルは無視できるので、それは使わない。
ると2項係数がk-1とkから計算するの同じことになる。

rule 90の定義：
``90 = 0x5a = 01011010```

```
XYZ XYZ XYZ XYZ XYZ XYZ XYZ XYZ
111 110 101 100 011 010 001 000
 0   1   0   1   1   0   1   0
XY      XY      XY      XY 
1_1 1_0         0_1 0_0
 0   1           1   0
```

真中のセルは無視できるので、それは使わない。
2項係数とは別なものになる。
```

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
# 補足説明

引用部分は、英語版のWikipedia （文献[3]）から削除されている。

文献[4]をみると、この話は、XYだけをつかうルールのECAに限定するべきなようだ。

ここでのECAの定義では、初期値が{1,0,0…} に限定しているので、
ピラミッド様の rule 90 の絵は描けない。rule 90 への言及は参考とする。
*)

(**
# 文献

[1] https://mathworld.wolfram.com/ElementaryCellularAutomaton.html

[2] https://qiita.com/Lirimy/items/9e13b156d53a71e5b72f

[3] Cellular automaton [https://en.wikipedia.org/wiki/Cellular_automaton]

[4] https://www.wolframscience.com/nks/notes-6-6--general-associative-cellular-automaton-rules/
*)

(* END *)
