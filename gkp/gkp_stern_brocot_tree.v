(**
Stern–Brocot tree (スターン・ブロコット木)
========================

@suharahiromichi

2020/12/31
 *)

(**
# はじめに

[1.] の 4.5節と6.7節で扱われている
スターン・ブロコット木 (シュターン・ブロッコ・ツリー。以下、SBT) 
は二分木で、そのノードは既約分数になっています。

SBTのノードをルートからの道順

$$ [R^{a_0}; L^{a_1}; ...; R^{a_{n-2}}; L^{a_{n-1}}] $$

で表現するならば、これは有理数のひとつの表現になっています。
これを「スターン・ブロコット数表現 Stern-Brocot representation」と呼びます（以下、SBR）。
SBRと分数（連分数）との相互変換について考えてみます。

木なので再帰関数（漸化式）で定義するのは比較的容易ですが、
閉じた式で表現することがお題です。

関連して、任意のノードに対して左（右）の子を求める（単純な）方法を考えてみます。
これは[2.] も参照してください。


# 目次

- SBTの行列による表現

- SBRの再帰関数による定義

- リストのtakeとdrop

- リストのdropによる帰納法

- continuant、連分多項式 (Euler の K)

- K による表現と証明

- ノードの左（右）の子

- （おまけ）SBTのノードが既約になることの証明

*)

(**
# Stern-Brocot tree (SBT) の行列による表現

[1.] のようにSBTのノードを次で表現します。

```math
\begin{pmatrix}
q & p' \\
p & q'
\end{pmatrix}
```

このノードの値を次で表現します。
行列表現に対して $ f $ を適用することで値が得られることに注意してください。

```math
f (
\begin{pmatrix}
q & q' \\
p & p'
\end{pmatrix}
)
=
\frac{p + p'}{q + q'}
```

## ルート

ルートは以下で、

```math
\begin{pmatrix}
0 & 1 \\
1 & 0
\end{pmatrix}
```

その値は以下です。

```math
f (
\begin{pmatrix}
0 & 1 \\
1 & 0
\end{pmatrix}
)
=
\frac{1}{1} = 1
```


## 左側のノード

左側のノードは、行列 $ L^{a_n} $ を右から掛けることで得られます。
$n$ は左に下がる回数です。

```math
\begin{pmatrix}
q & q' \\
p & p'
\end{pmatrix}
\begin{pmatrix}
1 & a_n \\
0 & 1
\end{pmatrix}
=
\begin{pmatrix}
q & a_n\ (q + q') \\
p & a_n\ (p + p')
\end{pmatrix}
```


## 右側のノード

右側のノードは、行列 $ R^{a_n} $ を右から掛けることで得られます。
$n$ は右に下がる回数です。

```math
\begin{pmatrix}
q & q' \\
p & p'
\end{pmatrix}
\begin{pmatrix}
1 & 0 \\
a_n & 1
\end{pmatrix}
=
\begin{pmatrix}
a_n\ (q + q') & q' \\
a_n\ (p + p') & p'
\end{pmatrix}
```


# Stern-Brocot representation (SBR) の再帰関数による定義

SBRのサイズは偶数として $n$ で示します。
表現の一意性のために要素は0を許さないことにします（1以上）が、
最初と最後だけは 0 を許すことにします（$a_{0} \ge 0$、$a_{n-1} \ge 0$）。

```math
\begin{eqnarray}
SB([]) &=&
\begin{pmatrix}
1 & 0 \\
0 & 1
\end{pmatrix}

\\

SB([R^{a_0}; ... ; L^{a_{n-3}}; R^{a_{n-2}}; L^{a_{n-1}}) &=&
SB([R^{a_0}; ... ; L^{a_{n-3}}])\ 

\begin{pmatrix}
1 & 0 \\
a_n & 1
\end{pmatrix}
\
\begin{pmatrix}
1 & a_{n+1} \\
0 & 1
\end{pmatrix}
\end{eqnarray}
```

*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)
Require Import Program.Wf.                  (* Program wf *)
(* Import Program とすると、リストなど余計なものがついてくるので、Wfだけにする。 *)

Require Import Extraction.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(**
# 文献

[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition

[1'] 有澤、安村、萩野、石畑訳、「コンピュータの数学」共立出版


[2.] Stern-Brocot tree

https://en.wikipedia.org/wiki/Stern-Brocot_tree
 *)

(* END *)