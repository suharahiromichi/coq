(**
上昇階乗冪と多重集合係数
========================

@suharahiromichi

2020/06/30
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

Coq/MathComp の binomial.v ライブラリで遊んでいます。

ここで定義されているのは、
順列（下降階乗冪、 falling factorial）と、
組合せ（二項係数、binomial coeficient）です。

それらについては大抵の補題が証明されているので、
これらに良く似た（対応した）、上昇階乗冪 (rising factorial) と、
重複組合せ（多重集合係数、multiset coeficent）を定義して、
いくつかの性質を証明してみます。
*)
(**
## 定義

- 下降階乗冪は、nをからそれを含むm個の下降積です。
MathCompでは、「$n^\underline{m}$=``n^_m``」と表記します。

$$ n^\underline{m} = \prod_{k=1}^{m}(n - k + 1) $$

- 二項係数は、MathCompでは、

```math

{n\choose m}=C(n, m)
```

と表記します。次の漸化式で定義されます。

```math

\begin{eqnarray}
C(n, 0) &=& 1 \\
C(n, m) &=& C(n-1, m-1) C(n-1, m)\\
\end{eqnarray}
```

- 上昇階乗冪は、nをからそれを含むm個の上昇積です。
MathCompでは、「$n^\overline{m}$=``n^^m``」と表記します。

$$ n^\overline{m} = \prod_{k=1}^{m}(n + k - 1) $$


- 多重集合係数は、

```math

\left(\!\!{n\choose m}\!\!\right) = H(n, m)
```

と表記することにします。二項係数と同様に漸化式で定義されます。

```math

\begin{eqnarray}
H(n, 0) &=& 1 \\
H(n, m) &=& H(n-1, m) H(n, m-1)\\
\end{eqnarray}
```
*)
(**
## 目標

以下では、下降階乗冪と上昇階乗冪の関係：

$$ (n+m)^\underline{m} = (n+1)^\overline{m} $$

および、二項係数と多重集合係数の関係：

$$ C(n + m, m) = H(n + 1, m) $$

を証明することを目標にします。
なお、有理数は導入せず、自然数の割算と剰余を使います。

このとき、``d | n`` は n は d を割り切る（除数 | 被除数）こととし、
四則演算より優先度が低いものとします。

適宜括弧を補って表記します。
*)

(* END *)
