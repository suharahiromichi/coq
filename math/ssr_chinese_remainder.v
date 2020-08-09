(**
中国人の剰余定理
========================

@suharahiromichi

2020/08/05

# はじめに

中国人の剰余定理 (中国剰余定理、Chinese remainder theorem) [1][2] は、
連立一次合同式の解の存在と解の一意性を示すものです。
Coq/MathComp の ``div.v`` ライブラリ [3] には、
その解を求める関数(chinese)と定理の証明があります。

中国人の剰余定理の勉強を兼ねて、MathComp のchinese関数などについて調べてみます。
ここでは、関数や補題の説明が目的なので、形式的な証明を記述しているわけでありません。
``div.v`` は自然数の上で定義されているので、断りのないかぎり、定数や変数は自然数とします。
そのため、整数で説明されている一般的な説明とは異なる箇所もあります。

解だけを求めるのであれば、Coqのような定理証明系よりも、
Wolfram Mathematica のような数式処理システム [4] のほうがずっと手軽であことを
書き添えておきます。
*)

(**
# 定理の説明

## 解の存在

自然数 m と n が互いに素で、任意の自然数 a と b が与えられたとき、
連立合同式(1)には解 x が存在する。

```math

%%%%%\left\{
\begin{eqnarray}
x &=& a \pmod{m} \tag{1.1} \\
x &=& b \pmod{n} \tag{1.2} \\
\end{eqnarray}
%%%%%\right.

```

言い換えると、「互いに素な自然数mとnを法とする連立合同式には解がある」、あるいは、
「mとnが互いに素なら、mで割ってa余り、nで割ってb余る数xが存在する」。

## 解の一意性

式(1.1)(1.2)の別の解をyとするなら、(2)が成り立つ。

$$ y = x \pmod{m n} \tag{2} $$


言い換えると、「先の連立合同式の解は、$ m n $ を法として一意である」、あるいは、
「数xから、$ m n $ を繰り返し引いても足しても、題意を満たす」

また、式(2)より、最小の解y'は $$ y' = x \mod mn $$ であり、$$ 0 \le y' \lt mn $$ である。
 *)

(**
# 証明の概要

## 解の存在の証明

自然数mとnが互いに素なので、
次の不定方程式(3.1)(3.2)が成り立ち、解u、v、p、qが存在する。
この解は、拡張ユーグリッド互除法で求めることができる。これについては後述する。

```math

\begin{eqnarray}
m u - n v &=& 1 \tag{3.1} \\
n p - m q &=& 1 \tag{3.2} \\
\end{eqnarray}

```

式(1.1)(1.2)を満たすxのひとつは、式(4)で表すことができる。

```math

x = n p a + m u b \tag{4}

```

なぜなら、

```math

\begin{eqnarray}
m u &=& 1 + n v \tag{3'.1} \\
n p &=& 1 + m q \tag{3'.2} \\
\end{eqnarray}

```

(3'.1)(3'.2)を(4)に代入すると、

```math

\begin{eqnarray}
x &=& n p a + m u b \\
  &=& (1 + m q) a + m u b &=& a + m (q a + u b) \tag{4.1} \\
  &=& n p a + (1 + n v) b &=& b + n (p a + v b) \tag{4.2}
\end{eqnarray}

```

式(4.1)から式(1.1)が、
式(4.2)から式(1.2)が、
成り立つことがわかる。


## 解の一意性の証明

自然数mとnが互いに素なので、式(5.1)(5.2)が成り立つ。
ここで、$ m \mid{x} $ は m を除数とし、
「|」は四則演算より結合度が低いものとします。

```math

\begin{eqnarray}
m \mid{x - y} \tag{5.1} \\
n \mid{x - y} \tag{5.2}
\end{eqnarray}

```

なぜなら、

```math

\begin{eqnarray}
x &=& m s + a \\
y &=& m t + a \\
\end{eqnarray}

```

から、 $$ x - y = m (s - t) (= 0 \pmod{m}) $$ が成り立つため。


そして、式(5.1)(5.2)から、式(6)が成り立つ。

$$ m n \mid{x - y} \tag{6} $$

式(6)から、式(2)が成り立つ。
*)

(**
# 実際の計算例

## 簡単な例

### 問題

3で割って2余る、5で割って3余る最小の自然数を求める。すなわち、

```math

\begin{eqnarray}
x &=& 2 \pmod{3} \tag{11.1} \\
x &=& 3 \pmod{5} \tag{11.2} \\
x &<& 3・5
\end{eqnarray}

```

### 計算例

3と5は互いに素なので、

```math

\begin{eqnarray}
3 u - 5 v &=& 1 \tag{13.1} \\
5 p - 3 q &=& 1 \tag{13.2} \\
\end{eqnarray}

```

不定方程式(13.1)と(13.2)には解がある。

```math

\begin{eqnarray}
u &=& 2, v &=& 1 \\
p &=& 2, q &=& 3 \\
\end{eqnarray}

```

式(4)に代入すると、

```math

\begin{eqnarray}
x &=& n p a + m u b \\
  &=& 5 ・ 2 ・ a + 3 ・ 2 ・ b \\
  &=& 5 ・ 2 ・ 2 + 3 ・ 2 ・ 3 \\
  &=& 38
\end{eqnarray}

```

そして、$ 38 \mod 3・5 = 8 $ となる。

検算すると、

```math

\begin{eqnarray}
8 &=& 2 \pmod{3} \tag{11'.1} \\
8 &=& 3 \pmod{5} \tag{11'.2} \\
8 &<& 3・5
\end{eqnarray}

```

*)

(**
## 孫子算経の例

### 問題

3で割って2余る、5で割って3余る、7で割って2余る最小の自然数を求める。すなわち、

```math

\begin{eqnarray}
x' &=& 2 \pmod{3} \tag{21.1} \\
x' &=& 3 \pmod{5} \tag{21.2} \\
x' &=& 2 \pmod{7} \tag{21.3} \\
x' &<& 3・5・7
\end{eqnarray}

```
*)
(**
### 計算例

3で割った余り(式(11.1))と、5で割った余り(式(11.2))の連立については前節で示した。
その解 $ x = 8 $ は、本節の解 x' に対して、
式(2)から、$$ x' = 8 \pmod{3・5} \tag{22} $$ が成り立つはずである。

これと、7で割った余り(式(21.3))との連立を考えると、つぎの連立合同式を解けばよいことになる。

```math

\begin{eqnarray}
x' &=& 8 \pmod{3・5} \tag{22} \\
x' &=& 2 \pmod{7} \tag{21.3} \\
x' &<& 3・5・7
\end{eqnarray}

```


$ 15 (= 3・5) $ と 7 は互いに素なので、

```math

\begin{eqnarray}
15 u' - 7 v' &=& 1 \tag{23.1} \\
7 p' - 15 q' &=& 1 \tag{23.2} \\
\end{eqnarray}

```

不定方程式(23.1)と(23.2)には解がある。

```math

\begin{eqnarray}
u' &=& 1, v' &=& 2 \\
p' &=& 13, q' &=& 6 \\
\end{eqnarray}

```

式(4)に代入すると、

```math

\begin{eqnarray}
x' &=& n' p' a' + m' u' b' \\
  &=& 7 ・ 13 ・ a + 15 ・ 1 ・ b \\
  &=& 7 ・ 13 ・ 8 + 15 ・ 1 ・ 2 \\
  &=& 758
\end{eqnarray}

```

そして、$ 758 \mod 15・7 = 23 $ となる。

検算すると、

```math

\begin{eqnarray}
23 &=& 2 \pmod{3} \tag{21'.1} \\
23 &=& 3 \pmod{5} \tag{21'.2} \\
23 &=& 2 \pmod{7} \tag{21'.3} \\
23 &<& 3・5・7
\end{eqnarray}

```
*)


(**
# Coq/MathComp での定義と証明
*)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
## chinese 関数

連立合同式の解は chinese 関数で求められる。式(11)の例では、
 *)
Compute chinese 3 5 2 3.                    (* 38 *)
Compute chinese 3 5 2 3 %% (3 * 5).         (* 8 *)

(**
式(21)の例では、
*)
Compute chinese 15 7 8 2.                   (* 758 *)
Compute 758 %% (15 * 7).                    (* 23 *)

(**
計算式は、式(4)とまったく同じである。
 *)
Print chinese.
(* = fun m1 m2 r1 r2 : nat => r1 * m2 * (egcdn m2 m1).1 + r2 * m1 * (egcdn m1 m2).1 *)
(* = fun m  n  a  b  : nat => a  * n  * (egcdn n  m ).1 + b  * m  * (egcdn m  n ).1 *)

(**
ただし、

- ``egcdn n m`` は不定方程式 $ n p - m q = 1 $ の解 ``(p, q)``
- ``egcdn m n`` は不定方程式 $ m u - n v = 1 $ の解 ``(u, v)``


であり、さらに p と u を取り出している。

- ``(egcdn n m).1 = (p, q).1 = p``
- ``(egcdn m n).1 = (u, v).1 = u``
*)

(**
## 解の存在 (chinese_modl と chinese_modr 補題)

これらの補題は、chinese関数が、式(1.1)と式(1.2)を満たすことを述べてている。
すなわち、解の存在を示している。
*)
Check chinese_modl : forall m n : nat,
    coprime m n -> forall a b : nat, chinese m n a b = a %[mod m].

Check chinese_modr : forall m n : nat,
    coprime m n -> forall a b : nat, chinese m n a b = b %[mod n].


(**
## 解の一意性（chinese_mod 補題）

y と m と n が式(1.1)と式(1.2)を満たすとする。すなわち、自然数 a と b が存在して、

```math

\begin{eqnarray}
a &=& y \mod m \\
b &=& y \mod n \\
\end{eqnarray}

```

であるとき、``x = chiniese m n a b`` もまた、式(1.1)と式(1.2)を満たす。
``x = y`` とは限らないが、式(2)のとおり``m * n`` を法として合同である。

すなわち、chinese_mod 補題は、解の（$m n$を法とした）一意性を述べている。
*)
Check chinese_mod : forall m n : nat,
    coprime m n ->
    forall y : nat, y = chinese m n (y %% m) (y %% n) %[mod m * n].

(**
この補題の証明の途中で次の補題を使用しているが、みっつのyは異なっていてもよいので、
これは式(1)と式(2)の特別な場合である（[5]の式(4.42)）。

「=」の両辺はbool述語なので、「=」は「<->」の意味である。
*)
Check chinese_remainder : forall m n : nat,
    coprime m n ->
    forall x y : nat,
      (x == y %[mod m * n]) = (x == y %[mod m]) && (x == y %[mod n]).

(**
# 不定方程式の解

## 説明

自然数m と n が互いに素であるとき、不定方程式式(31)が解u、vを持つ。

$$ m u - n v = 1 \tag{31} $$

なお、次の式(32)は、両辺を$gcd(m,n)$で割ると、式(31)と同じ意味になる。

$$ m u - n v = gcd(m,u) \tag{32} $$

また、任意の整数kに対して、u'、v'も同様に解となります。

```math

\begin{eqnarray}
u' &=& u + k a \tag{33.1} \\
v' &=& v + k b \tag{33.2} \\
\end{eqnarray}

```

式(31)が成り立てば、式(4)は成り立つので、
不定方程式の解としては任意の解を使うことができる。


## 不定方程式の解の存在の証明

（追記する）


## 机上での計算例（その1）

$$ 3 u - 5 v = 1 \tag{41} $$ の解 u, vを求める。

互除法を適用すると

```math

\begin{eqnarray}
3 - 5・0 &=& 3 \tag{42} \\
5 - 3・1 &=& 2 \tag{43} \\
3 - 2・1 &=& 1 \tag{44} \\
\end{eqnarray}

```

式(42)を式(43)に代入すると、

```math

\begin{eqnarray}
5 - (3 - 5・0)・1 = 2 \\
3・(-1) - 5・(-1) = 2 \tag(43') \\
\end{eqnarray}

```

式(43')を式(44)を代入して、式(44')を得る。

```math

\begin{eqnarray}
3 - (3・(-1) - 5・(-1))・1 &=& 1 \\
3・2 - 5・1 &=& 1 \tag{44'} \\
\end{eqnarray}

```

式(44')から、次の解を得る。

$$ u = 2, v = 1 $$


## 机上での計算例（その2）

$$ 5 p - 3 q = 1 \tag{51} $$ の解 p, qを求める。

互除法を適用すると

```math

\begin{eqnarray}
5 - 3・1 &=& 2 \tag{52} \\
3 - 2・1 &=& 1 \tag{53} \\
\end{eqnarray}

```

式(52)を式(53)を代入して、式(53')を得る。

```math

\begin{eqnarray}
3 - (5 - 3・1)・1 &=& 1 \\
-5 + 3 + 3 &=& 1 \\
5・(-1) - 3・(-2) &=& 1 \tag{53'} \\
\end{eqnarray}

```

式(53')から、次の解を得る。

$$ u = -1, v = -2 $$

式(4)に代入するならこの値でも構わないのだが、
MathCompにあわせて自然数にする場合は、
式(33)の $ k = 1 $ として、

```math

\begin{eqnarray}
2 &=& -1 + 1・3 \\
3 &=& -1 + 1・5 \\
\end{eqnarray}

```

から、次の解を得る。

$$ u = 3, v = 5 $$

（直接 自然数 の解をもとめる方法を調べる。
また MathCompの定義に沿った説明に入れ替える。）


## Coq/MathComp での計算例

式(31)または式(32)に不定方程式はユーグリッドの互除法で解くことができます。
MathCompでは、拡張GCD関数を使って、以下で計算できます。

```coq

egcdn m n = (u, v)

```
*)

Compute egcdn 3 5.                          (* (2, 1) *)
Compute egcdn 5 3.                          (* (2, 3) *)

(**
# 文献

[1] 中国の剰余定理

https://ja.wikipedia.org/wiki/中国の剰余定理


[2] 中国剰余定理 (CRT) の解説と、それを用いる問題のまとめ

https://qiita.com/drken/items/ae02240cd1f8edfc86fd


[3] math-comp div.v

https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/div.v


[4] Wolfram言語 ＆ システム ドキュメントセンター ChineseRemainder

https://reference.wolfram.com/language/ref/ChineseRemainder.html


[5] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition
 *)

(* END *)
