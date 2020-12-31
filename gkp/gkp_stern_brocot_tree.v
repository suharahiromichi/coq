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

$$ R^{a_0}; L^{a_1}; ...; R^{a_{n-2}}; L^{a_{n-1}} $$

で表現するならば、これは有理数のひとつの表現になっています。
これを「スターン・ブロコット数表現 Stern-Brocot representation」と呼びます（以下、SBR）。
SBRと分数（連分数）との相互変換について考えてみます。

木なので再帰関数（漸化式）で定義するのは比較的容易ですが、
閉じた式で表現することがお題です。

関連して、任意のノードに対して左（右）の子を求める（単純な）方法を考えてみます。
これは[2.] も参照してください。


# 目次

- リストのtakeとdrop

- SBTの行列による表現

- SBRの再帰関数による定義

- リストのdropによる帰納法

- continuant、連分多項式 (Euler の K)

- K による表現と証明

- ノードの左（右）の子

- （おまけ）SBTのノードが既約になることの証明

*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import ssromega.
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)
Require Import Program.Wf.                  (* Program wf *)
(* Import Program とすると、リストなど余計なものがついてくるので、Wfだけにする。 *)

(* MathComp の belast の定義を避けて、自分で定義したものを補題込みで使う。 *)
Require Import csm_4_4_x_seq_head_last.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(**
# リストのtakeとdrop
 *)

Section TakeDropNat.
  Definition take_head s := head 0 s.
  Definition drop_head (s : seq nat) := behead s.
  Definition take_last s := last 0 s.
  (* see. csm_4_4_x_seq_head_last *)
  Print belast'.
  Definition drop_last (s : seq nat) := belast' s.
End TakeDropNat.
Notation "↑ s" := (take_head s) (at level 53, no associativity).
Notation "↓ s" := (drop_head s) (at level 51, no associativity).
Notation "s ↑" := (take_last s) (at level 54, no associativity).
Notation "s ↓" := (drop_last s) (at level 52, no associativity).

Section TakeDropNatPair.
  Definition take_head_natpair s := head (0, 0) s.
  Definition drop_head_natpair (s : seq (nat * nat)) := behead s.
  Definition take_last_natpair s := last (0, 0) s.
  Definition drop_last_natpair (s : seq (nat * nat)) := belast' s.
End TakeDropNatPair.
Notation "⇑ s" := (take_head_natpair s) (at level 53, no associativity).
Notation "⇓ s" := (drop_head_natpair s) (at level 51, no associativity).
Notation "s ⇑" := (take_last_natpair s) (at level 54, no associativity).
Notation "s ⇓" := (drop_last_natpair s) (at level 52, no associativity).

Section TakeDrop1.
  Compute ↑[:: 1; 2; 3].                   (* 1 *)
  Compute [:: 1; 2; 3]↑ .                  (* 3 *)
  Compute ↓[:: 1; 2; 3].                   (* [:: 2; 3] *)

  Compute ↓[:: 1; 2; 3].                   (* [:: 2; 3] *)
  Compute ↑↓[:: 1; 2; 3].                 (* 2 *)
  Compute ↓↓[:: 1; 2; 3].                 (* [:: 3] *)

  Compute [:: 1; 2; 3]↓.                   (* [:: 1; 2] *)
  Compute [:: 1; 2; 3]↓↑.                 (* 2 *)
  Compute [:: 1; 2; 3]↓↓.                 (* [:: 1] *)

(**
drop のほうを優先する。dropしてtake できるように。
 *)
  Compute ↓[:: 1; 2; 3]↑.                 (* 3 *)
  Compute ↑[:: 1; 2; 3]↓.                 (* 1 *)
  
(**
dropどうしならどちらでも一緒だが、head のほうを優先する。
 *)
  Compute (↓[:: 1; 2; 3])↓.               (* [:: 2] *)

(**
drop head と drop last の順番がどちらでもよいことを証明する。
 *)
  Lemma drop_head_last s : (↓s)↓ = ↓(s↓).
  Proof.
    case: s => // a s.
    rewrite [LHS]/=.
    elim/last_ind : s => // s a' _.         (* 場合分け。帰納法の前提は捨てる。 *)
    rewrite /drop_last -rcons_cons !belast'_rcons.
    done.
  Qed.

(**
寸法が十分なら、dropしたあとにtakeしてもおなじであることを証明する。
*)
  Compute ↑[:: 1].                         (* 1 *)
  Compute ↑[:: 1]↓.                       (* 0 *)
  Compute ↑[:: 1; 2].                      (* 1 *)
  Compute ↑[:: 1; 2]↓.                    (* 1 *)

  Lemma take_head_drop_last s : 1 < size s -> ↑s↓ = ↑s.
  Proof.
    case: s => // a s.
    elim/last_ind : s => // s a' _ H.       (* 寸法の前提がここで使う。 *)
    rewrite /drop_last -rcons_cons !belast'_rcons.
    done.
  Qed.

(**
寸法が十分なら、dropしたあとにtakeしてもおなじであることを証明する。
*)
  Compute [:: 1]↑.                         (* 1 *)
  Compute ↓[:: 1]↑.                       (* 0 *)
  Compute [:: 1; 2]↑.                      (* 2 *)
  Compute ↓[:: 1; 2]↑.                    (* 2 *)

  Lemma take_last_drop_head s : 1 < size s -> ↓s↑ = s↑.
  Proof.
    case: s => // a s.
    elim/last_ind : s => // s a' _ H.       (* 寸法の前提がここで使う。 *)
    rewrite /=.
    rewrite /take_last -rcons_cons !last_rcons.
    done.
  Qed.

End TakeDrop1.  

(**
# Stern-Brocot tree (SBT) の行列による表現

[1.] のようにSBTのノードを次で表現します。

```math
\begin{pmatrix}
q & v \\
p & u
\end{pmatrix}
```

このノードの値を次で表現します。
行列表現に対して $ f $ を適用することで値が得られることに注意してください。

```math
f (
\begin{pmatrix}
q & v \\
p & u
\end{pmatrix}
)
=
\frac{p + u}{q + v}
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
q & v \\
p & u
\end{pmatrix}
L^a
=
\begin{pmatrix}
q & v \\
p & u
\end{pmatrix}
\begin{pmatrix}
1 & a \\
0 & 1
\end{pmatrix}
=
\begin{pmatrix}
q & a\ q + v \\
p & a\ p + u
\end{pmatrix}
```


## 右側のノード

右側のノードは、行列 $ R^a $ を右から掛けることで得られます。
$a$ は右に下がる回数です。

```math
\begin{pmatrix}
q & v \\
p & u
\end{pmatrix}
R^a
=
\begin{pmatrix}
q & v \\
p & u
\end{pmatrix}
\begin{pmatrix}
1 & 0 \\
a & 1
\end{pmatrix}
=
\begin{pmatrix}
q + a\ v & v \\
p + a\ p & u
\end{pmatrix}
```


# Stern-Brocot representation (SBR) の再帰関数による定義

SBRを $ R^{a_0}; L^{a_1}; ...; R^{a_{n-2}}; L^{a_{n-1}} $ で示します。

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

SB(R^{a_0}; ... ; L^{a_{n-3}}; R^{a_{n-2}}; L^{a_{n-1}}) &=&
SB(R^{a_0}; ... ; L^{a_{n-3}})\ 

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

Section SBR.
(**
## ノードの定義

SBT のノードは直積の直積で表現し、常識的な順番とします。

```math
\begin{pmatrix}
q & v \\
p & u
\end{pmatrix}
=
((q,\ v),\ (p,\ u))
```
*)
  Definition SBNode := ((nat * nat) * (nat * nat))%type.
  
  Definition IDENT : SBNode := ((1, 0), (0, 1)).
  Definition LEFT (a : nat) : SBNode := ((1, a),
                                         (0, 1)).
  Definition RIGHT (a : nat) : SBNode := ((1, 0),
                                          (a, 1)).  
  Definition NODE (q p v u : nat) : SBNode := ((q, v),
                                               (p, u)).
  Local Definition q_ (N : SBNode) := N.1.1.
  Local Definition p_ (N : SBNode) := N.2.1.
  Local Definition v_ (N : SBNode) := N.1.2.
  Local Definition u_ (N : SBNode) := N.2.2.
  
  Lemma NODEeq (N : SBNode) : ((q_ N, v_ N),
                               (p_ N, u_ N)) = N.
  Proof.
      by rewrite -!surjective_pairing.
  Qed.

  Goal LEFT 0 = IDENT.
  Proof.
    by rewrite /LEFT /IDENT.
  Qed.

  Goal RIGHT 0 = IDENT.
  Proof.
    by rewrite /RIGHT /IDENT.
  Qed.

(**
## ノードの値の計算
*)

  Definition SBFrac:= (nat * nat)%type.
  Definition SBf (N : SBNode) : SBFrac := (p_ N + u_ N, q_ N + v_ N).
  
(**
## 掛け算の定義

掛け算の定義と関連する補題を証明します。
*)
  Definition mul (N N' : SBNode) := 
    ((q_ N * q_ N' + v_ N * p_ N', q_ N * v_ N' + v_ N * u_ N'),
     (p_ N * q_ N' + u_ N * p_ N', p_ N * v_ N' + u_ N * u_ N')).
  Notation "N * N'" := (mul N N').
  
  Lemma mulIr (N : SBNode) : N * IDENT = N.
  Proof.
    rewrite /mul /NODE /IDENT /q_ /p_ /v_ /u_ //=.
    rewrite !muln0 !muln1 !addn0 !add0n.
      by rewrite NODEeq.
  Qed.

  Lemma mulIl (N : SBNode) : IDENT * N = N.
  Proof.
    rewrite /mul /NODE /IDENT /q_ /p_ /v_ /u_ //=.
    rewrite !mul0n !mul1n !addn0 !add0n.
      by rewrite NODEeq.
  Qed.

  Lemma mulLa (N : SBNode) (a : nat) :
    N * LEFT a = ((q_ N, a * q_ N + v_ N),
                  (p_ N, a * p_ N + u_ N)).
  Proof.
    rewrite /mul /NODE /LEFT /q_ /p_ /v_ /u_ //=.
    rewrite !muln1 !muln0 !addn0.
    rewrite ![(_ * a)%N]mulnC.
    done.
  Qed.

  Lemma mulRa (N : SBNode) (a : nat) :
    N * RIGHT a = ((q_ N + a * v_ N, v_ N),
                   (p_ N + a * u_ N, u_ N)).
  Proof.
    rewrite /mul /NODE /RIGHT /q_ /p_ /v_ /u_ //=.
    rewrite !muln1 !muln0 !add0n.
    rewrite ![(_ * a)%N]mulnC.
    done.
  Qed.

(**
## SBR から ノードへの変換関数

SBR は、

$$ R^{a_0}; L^{a_1}; ...; R^{a_{n-2}}; L^{a_{n-1}} $$

の肩の数字の2個づつのリストとして、つぎのように表記します。

```
[:: (a_0, a_1); ... (a_(n-2), a_(n-1))]
```
*)  
  Function SB (s : seq (nat * nat)) {measure size s} : SBNode :=
    match s with
    | [::] => IDENT
    | _ => SB (s⇓) * RIGHT (s⇑.1) * LEFT (s⇑.2)
    end.
  Proof.
    move=> s a s' H.
    apply/ltP.
    (* see. csm_4_4_x_seq_head_last *)
    rewrite /drop_last size_belast'.
    done.
  Qed.
  Check SB_equation.
  
  Lemma SBI : SB [::] = IDENT.
  Proof. by rewrite SB_equation. Qed.

(**
## 計算例
*)  
  Goal SBf (SB [:: (0, 1)]) = (1, 2).
  Proof.
    rewrite /SBf SB_equation //=.
    rewrite !SBI /IDENT /q_ /p_ /v_ /u_.
    done.
  Qed.

  Goal SBf (SB [:: (0, 4)]) = (1, 5).
  Proof.
    rewrite /SBf SB_equation //=.
    rewrite !SBI /IDENT /q_ /p_ /v_ /u_.
    done.
  Qed.
  
  Goal SBf (SB [:: (1, 1); (1, 0)]) = (5, 3).
  Proof.
    rewrite /SBf 2!SB_equation //=.
    rewrite SBI /RIGHT /LEFT /IDENT /q_ /p_ /v_ /u_.
    done.
  Qed.

  Goal SBf (SB [:: (1, 1); (1, 1)]) = (8, 5).
  Proof.
    rewrite /SBf 2!SB_equation //=.
    rewrite SBI /RIGHT /LEFT /IDENT /q_ /p_ /v_ /u_.
    done.
  Qed.
  
End SBR.

(**
# リストのdropによる帰納法
 *)



(**
# 文献

[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition

[1'] 有澤、安村、萩野、石畑訳、「コンピュータの数学」共立出版


[2.] Stern-Brocot tree

https://en.wikipedia.org/wiki/Stern-Brocot_tree
 *)

(* END *)


