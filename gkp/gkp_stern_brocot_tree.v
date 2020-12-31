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

ルートは単位行列で、

```math
\begin{pmatrix}
1 & 0 \\
0 & 1
\end{pmatrix}
```

その値は以下になります。

```math
f (
\begin{pmatrix}
1 & 0 \\
0 & 1
\end{pmatrix}
)
=
\frac{1}{1} = \frac{0 + 1}{1 + 0} = 1
```


## 左側のノード

左側のノードは、行列 $ L^a $ を右から掛けることで得られます。
$a$ は左に下がる回数です。

```math
\begin{pmatrix}
q & q' \\
p & p'
\end{pmatrix}
L^a
=
\begin{pmatrix}
q & q' \\
p & p'
\end{pmatrix}
\begin{pmatrix}
1 & a \\
0 & 1
\end{pmatrix}
=
\begin{pmatrix}
q & a\ q + q' \\
p & a\ p + p'
\end{pmatrix}
```


## 右側のノード

右側のノードは、行列 $ R^a $ を右から掛けることで得られます。
$a$ は右に下がる回数です。

```math
\begin{pmatrix}
q & q' \\
p & p'
\end{pmatrix}
R^a
=
\begin{pmatrix}
q & q' \\
p & p'
\end{pmatrix}
\begin{pmatrix}
1 & 0 \\
a & 1
\end{pmatrix}
=
\begin{pmatrix}
q + a\ q' & q' \\
p + a\ p` & p'
\end{pmatrix}
```


# Stern-Brocot representation (SBR) の再帰関数による定義

SBRを $ [R^{a_0}; L^{a_1}; ...; R^{a_{n-2}}; L^{a_{n-1}}] $ で示します。

ただし、SBRのサイズは偶数として $n \ge 0$ で示します。
表現の一意性のために、各要素の値は0を許さないことにします（\ge 1）が、
最初と最後の要素だけは 0 を許すことにします。

$a_{0} = 0$ のときは 1未満の数、
$a_{n-1} = 0$ のときは最後のノードが親の右側にあることを示します。

SBR を リスト(seq)の s としたときに、
前章で定義したSBTのノードの表現に変換する関数を $SB(s)$ で定義します。

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
a_{n-2} & 1
\end{pmatrix}
\
\begin{pmatrix}
1 & a_{n-1} \\
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


