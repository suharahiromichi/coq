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

- continuant、連分多項式 (Gauss の H と Euler の K)

- K による表現と証明

- （おまけ）ノードの左（右）の子

- （おまけ）SBTのノードが既約になることの証明

*)

From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
From common Require Import ssrinv.
From common Require Import ssromega.
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)
(* Require Import Program.Wf. *)            (* Program wf *)
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

(**
take drop したものを cons して戻ることを証明する。
 *)
  Lemma cons_take_dropE s : 1 <= size s -> ↑s :: ↓s = s.
  Proof. by case: s. Qed.

  Lemma cons_take_take_dropE s : 2 <= size s -> ↑s :: ↑↓s :: (↓↓s) = s.
  Proof.
    case: s => //= a s Hs.
    by rewrite cons_take_dropE.
  Qed.
  
(**  
rev に関する補題を証明する。
*)
  Lemma rev_take_head s : ↑(rev s) = s↑.
  Proof.
    elim/last_ind : s => // s a _.
    rewrite /take_last last_rcons.
    rewrite rev_rcons /=.
    done.
  Qed.
  
  Lemma rev_take_tail s : (rev s)↑ = ↑s.  (* tail_rev *)
  Proof.
    elim: s => // a s _ /=.    
    rewrite /take_last rev_cons last_rcons.
    done.
  Qed.
  
  Lemma rev_drop_head s : ↓(rev s) = rev (s↓).
  Proof.
    elim/last_ind : s => // s a _.
    rewrite /drop_last belast'_rcons.
    rewrite rev_rcons.
    done.
  Qed.
  
  Lemma rev_drop_tail s : (rev s)↓ = rev (↓s). (* body_rev *)
  Proof.
    elim: s => // a s _ /=.
    rewrite /drop_last rev_cons !belast'_rcons.
    done.
  Qed.

(**
寸法についての補題を証明しておきます。
*)
  Lemma size_drop_head s : size (↓s) = (size s).-1.
  Proof.
    by rewrite size_behead.
  Qed.
  
  Lemma size_drop_tail s : size (s↓) = (size s).-1.
  Proof.
    by rewrite size_belast'.    
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

の肩の数字のリストとして、つぎのように表記します。
リストの寸法は偶数であることを暗黙の前提としています（見直すこと）。

```
[:: a_0; a_1; ... a_(n-2); a_(n-1)]
```

SBR からノードへ変換する関数は、次のように定義されます。
先に定義したdropを使用しているため、Function コマンドを使用して、
引数のリストのサイズが減少することを明示的に示す必要があります。

csm_4_4_x_seq_head_last.v で証明した補題 size_belast' を使用しています。
*)
  Function SB (s : seq nat) {measure size s} : SBNode :=
    match s with
    | [::] => IDENT
    | _ => SB (s↓↓) * RIGHT (s↓↑) * LEFT (s↑)
    end.
  Proof.
    move=> s a s' H.
    apply/ltP.
    (* see. csm_4_4_x_seq_head_last *)
    rewrite /drop_last 2!size_belast' /=.
    by ssromega.
  Defined.
  
(**
Functon コマンドによって、関数の定義を簡約する補題が生成されています。
*)  
  Check SB_equation.                        (* 略 *)

  Lemma SBI : SB [::] = IDENT.
  Proof. by rewrite SB_equation. Qed.
  
(**
## 計算例
*)  
  (*                  R  L  R  L *)
  Compute SBf (SB [:: 0; 1]).               (* 1/2 *)
  Compute SBf (SB [:: 0; 4]).               (* 1/5 *)
  Compute SBf (SB [:: 1; 0]).               (* 2/1 *)
  Compute SBf (SB [:: 1; 1]).               (* 3/2 *)

  (* SB の引数は 2以上の偶数に制限すること。XXXX *)
  Compute SBf (SB [:: 1; 1; 1]).            (* 3/5 *)

  Compute SBf (SB [:: 1; 1; 1; 0]).         (* 5/3 *)
  Compute SBf (SB [:: 1; 1; 1; 1]).         (* 8/5 *)
  Compute SBf (SB [:: 2; 2]).               (* 7/3 *)

End SBR.
Notation "N * N'" := (mul N N').

(**
# リストのdropによる帰納法

SBの定義において、Functionコマンドが生成した帰納法は以下です。
*)

Check SB_ind.

(**
使いやすい補題のかたちにしておきます。
*)
Lemma SB_cond (s : seq nat) :
  (match s with [::] => False | _ :: _ => True end) -> 1 <= size s.
Proof.
    by case: s.
Qed.

Lemma SB_ind' : forall P : seq nat -> SBNode -> Prop,
    (forall a0 a1 : nat, P [:: a0; a1] ((1, a1), (a0, a0 * a1 + 1))) ->
    (forall s : seq nat,
        4 <= size s ->
        P (s↓↓) (SB (s↓↓)) ->
        P s (SB (s↓↓) * RIGHT (s↓↑) * LEFT (s↑))) ->
    forall s : seq nat, P s (SB s).
Proof.
  move=> P H1 IH s.
  functional induction (SB s) => //=.
  - admit.                                  (* P [::] IDENT *)
  - apply: IH.
    + move/SB_cond in y.                    (* 0 < size s *)
      admit.                                (* 3 < size s *)
    + done.
Admitted.
(**
この帰納法が証明できないのは、SB関数自体に定義が悪いからである。
*)

(**
# continuant、連分多項式

文献[1.]の Euler の K を導入します。
その前に Gauss の H を導入して、両者がおなじであることを証明しておきます。
H を使用すると K の証明が容易になる場合があるからです。

## Gauss の H
 *)
Section GAUSSH.
  
  Function GaussH (s : seq nat) {measure size s} : nat :=
    match s with
    | [::] => 1
    | [:: n] => n
    | n0 :: n1 :: s' => n0 * GaussH (n1 :: s') + GaussH s'
    end.
  Proof.
    - move=> s n0 l n1 s' H1 H2.
      apply/ltP => /=.
      by ssromega.
    - move=> s n0 l n1 s' H1 H2.
      apply/ltP => /=.
      by ssromega.
  Defined.
  
  Compute GaussH [:: 3; 3; 1; 2].           (* 36 *)
  Compute GaussH [:: 3; 1; 2].              (* 11 *)
  
  Lemma GaussH1 : GaussH [::] = 1.
  Proof. done. Qed.

  Lemma GaussHn n : GaussH [:: n] = n.
  Proof. done. Qed.
  
  Lemma GaussHE (n0 n1 : nat) (s : seq nat) :
    GaussH (n0 :: n1 :: s) = n0 * GaussH (n1 :: s) + GaussH s.
  Proof.
    by rewrite GaussH_equation.
  Qed.

  Lemma GaussHE' (s : seq nat) :
    2 <= size s ->
    GaussH s = (↑s) * GaussH (↓s) + GaussH (↓↓s).
  Proof.
    case: s => //= n0 s.
    case: s.
    + done.
    + move=> n1 s Hs.
      by rewrite GaussH_equation.
  Qed.
  
  Lemma GaussHEr (n0 n1 : nat) (s : seq nat) :
    GaussH (rcons (rcons s n1) n0) = n0 * GaussH (rcons s n1) + GaussH s.
  Proof.
    functional induction (GaussH s).
    - rewrite GaussHE /GaussH /=.
      by rewrite mulnC.
    - rewrite GaussHE /GaussH /=.
    (* n * (n1 * n0 + 1) + n0 = n0 * (n * n1 + 1) + n *)
      rewrite !mulnDr !mulnA !muln1.
      rewrite ?addnA addnAC.                (* n を最後に。 *)
      rewrite ?mulnA mulnAC.                (* n1 を最後に。 *)
      rewrite -?mulnA mulnCA.               (* n0 を最初に。 *)
      done.
    - rewrite /=.
      rewrite GaussHE IHn0 /=.
      rewrite GaussHE IHn /=.
      rewrite !mulnDr.
      rewrite ?addnA.
      rewrite [(n2 * (n0 * GaussH (n3 :: rcons s' n1)))%nat]mulnCA.
      by ssromega.
  Qed.
  
(*
  Lemma GaussHEr' (s : seq nat) :
    2 <= size s ->
    GaussH s = (s↑) * GaussH (s↓) + GaussH (s↓↓).
  Proof.
  Abort.
*)
  
  Lemma GaussH__GaussH_rev s : GaussH s = GaussH (rev s).
  Proof.
    functional induction (GaussH s) => //.
    rewrite !rev_cons.
    rewrite GaussHEr.
    rewrite -rev_cons.
    rewrite IHn IHn0.
    done.
  Qed.
End GAUSSH.

(**
## Euler の K
 *)
Section EULERK.
  
  Function EulerK (s : seq nat) {measure size s} : nat :=
    match s with
    | [::] => 1
    | [:: n] => n
    | _ => s↑ * EulerK (s↓) + EulerK (s↓↓)
    end.
  - move=> s n s' n' s'' H1 H2.
    apply/ltP.
    rewrite 2!size_belast' /=.
    by ssromega.    
  - move=> s n s' n' s'' H1 H2.
    apply/ltP.
    rewrite size_belast' /=.
    done.
  Defined.

(**
実行例  
 *)
  Compute EulerK  [:: 3; 3; 1; 2].          (* 36 *)
  Compute EulerK  [:: 3; 1; 2].             (* 11 *)

(**
EukerK の定義に出現する条件式に関する補題を証明しておきます。
*)
  Lemma EK_cond (s : seq nat) :
    (match s with [:: _, _ & _] => True | _ => False end) -> 2 <= size s.
  Proof.
    case: s => // a s.
    case: s => //.
  Qed.
  
(**
EulerK の再帰の1回分を補題にする。
*)
  Lemma EulerK0 : EulerK [::] = 1.
  Proof. done. Qed.

  Lemma EulerK1 a : EulerK [:: a] = a.
  Proof. done. Qed.
  
  Lemma EulerK2 a0 a1 : EulerK [:: a0; a1] = a0 * a1 + 1.
  Proof.
    rewrite EulerK_equation.
    rewrite /take_last /=.
    rewrite EulerK1 EulerK0.
    by rewrite mulnC.
  Qed.
  
  Lemma EulerKE s :
    2 <= size s ->
    EulerK s = s↑ * EulerK (s↓) + EulerK (s↓↓).
  Proof.
    case: s => //= n0 s.
    case: s.
    + done.
    + move=> n1 s Hs.
      by rewrite EulerK_equation.
  Qed.
  
(**
### EulerK と GaussH が同じ
*)  
  Lemma EulerK_rev__GaussH s : EulerK (rev s) = GaussH s.
  Proof.
    functional induction (GaussH s) => [//= | //= |].
    rewrite EulerKE.
    - rewrite rev_take_tail 2!rev_drop_tail.
      rewrite IHn -IHn0.
      done.
    - rewrite size_rev.
      done.
  Qed.
  
  Lemma EulerK__GaussH s : EulerK s = GaussH s.
  Proof.
    rewrite -(revK s).
    rewrite EulerK_rev__GaussH GaussH__GaussH_rev.
    rewrite revK.
    done.
  Qed.

  Lemma EulerKEr (s : seq nat) :
    2 <= size s ->
    EulerK s = (↑s) * EulerK (↓s) + EulerK (↓↓s).
  Proof.
    case: s => //= n0 s.
    case: s.
    + done.
    + move=> n1 s Hs /=.
      rewrite 3!EulerK__GaussH.
      by apply: GaussHE.
  Qed.
  
  Lemma EulerK__EulerK_rev s : EulerK s = EulerK (rev s).
  Proof.
(*
    functional induction (EulerK s) => //=.
    rewrite -rev_drop_head in IHn.
    rewrite -2!rev_drop_head in IHn0.
    rewrite IHn IHn0.
    rewrite -rev_take_head.
    rewrite -EulerKEr => //.
    (* Goal : 1 < size (rev s) *)
    move/EK_cond in y.
    rewrite size_rev.
    done.
    Restart.
*)
    rewrite 2!EulerK__GaussH.
    by rewrite -GaussH__GaussH_rev.
  Qed.
End EULERK.

(**
# K による表現と証明

SB関数を EulerK で表現できることを証明する。
 *)
Lemma SB_RIGHT_SB s :
  4 <= size s -> 
  ((EulerK (↓(s↓↓)↓), EulerK (↓(s↓↓))),
   (EulerK (s↓↓↓), EulerK (s↓↓))) * RIGHT (s↓↑)
  = ((EulerK (↓s↓), EulerK (↓s↓↓)),
     (EulerK (s↓), EulerK (s↓↓))).
Proof.
  move=> Hs.
  rewrite mulRa.
  rewrite /q_ /p_ /v_ /u_ //=.
  f_equal; f_equal.
  - rewrite addnC.
    rewrite (@EulerKE (↓s↓)).
    + rewrite 4!drop_head_last.
      rewrite take_last_drop_head.
      * done.
      * rewrite size_drop_tail.
        by ssromega.
    + rewrite size_drop_tail size_drop_head.
      by ssromega.
  - rewrite 2!drop_head_last.
    done.
  - rewrite addnC.
    rewrite (@EulerKE (s↓)).
    + done.
    + rewrite size_drop_tail.
      by ssromega.
Qed.

Lemma SB_RIGHT_LEFT_SB s :
  4 <= size s -> 
  ((EulerK (↓(s↓↓)↓), EulerK (↓(s↓↓))),
   (EulerK (s↓↓↓), EulerK (s↓↓))) * RIGHT (s↓↑) * LEFT (s↑)
  = ((EulerK (↓s↓), EulerK (↓s)),
     (EulerK (s↓), EulerK s)).
Proof.
  move=> Hs.
  rewrite SB_RIGHT_SB.
  - rewrite mulLa.
    rewrite /q_ /p_ /v_ /u_ //=.
    f_equal.
    + rewrite (@EulerKE (↓s)).
      * rewrite drop_head_last take_last_drop_head.
        ** done.
        ** by ssromega.
      * rewrite size_drop_head.
        by ssromega.
    + rewrite (@EulerKE s).
      * done.
      * by ssromega.
  - done.
Qed.

(**
証明したい定理
 *)

Definition SBK (s : seq nat) := ((EulerK (↓s↓), EulerK (↓s)),
                                 (EulerK (s↓), EulerK s)).

Theorem SB_EulerK s : 4 <= size s -> SB s = SBK s.
Proof.
  rewrite /SBK.
  move=> Hsize.
  apply SB_ind'.
  - move=> a0 a1 /=.
    by rewrite /IDENT EulerK0 2!EulerK1 EulerK2.
  - move=> s' Hsize' IHs.
    rewrite IHs.
    rewrite SB_RIGHT_LEFT_SB.
    + done.
    + done.
Qed.
(* ここで使った帰納法の証明はできていない。SB 関数の定義が悪いので、見直すこと！ *)

(* functional induction を直接使用しても、同様にうまくいかない。 *)
Theorem SB_EulerK' s : 4 <= size s -> SB s = SBK s.
Proof.
  rewrite /SBK.
  move=> Hs.
  functional induction (SB s) => //=.
  rewrite IHs0.
  - rewrite SB_RIGHT_LEFT_SB.
    * done.
    * by ssromega.
  - rewrite 2!size_drop_tail.
    rewrite -subn2.
    (* 3 < size _x - 2 *)
Admitted.                                   (* XXXXXX *)

(**
# （おまけ）ノードの左（右）の子

SBT のノードが連分数であることを示す [1.] (式 6.139) を証明する。
 *)
Section NUM_DEN.
  
  (* (式 6.139) *)
  Lemma SBR_num_den s : 4 <= size s ->
                        SBf (SB s) = (EulerK (rcons s 1),      (* 分子 *)
                                      EulerK (rcons (↓s) 1)). (* 分母 *)
  Proof.
    move=> Hsize.
    rewrite SB_EulerK /SBK /SBf /q_ /p_ /v_ /u_ //=.
    f_equal.
    - rewrite (@EulerKE (rcons s 1)).         (* 分子 *)
      + rewrite /take_last last_rcons mul1n.
        rewrite /drop_last belast'_rcons.
        by rewrite addnC.
      + rewrite size_rcons.
        by ssromega.
    - rewrite (@EulerKE (rcons (↓s) 1)).     (* 分子 *)
      + rewrite /take_last last_rcons mul1n.
        rewrite /drop_last belast'_rcons.
        by rewrite addnC.
      + rewrite size_rcons size_drop_head.
        by ssromega.
  Qed.
  
(**
連分数を分数に変換する関数

ssr_cont_fract.v を参照のこと。
*)
  Fixpoint cf2f (sa : seq nat)  : (nat * nat) :=
    match sa with
    | a :: sa' =>
      (a * (cf2f sa').1 + (cf2f sa').2, (cf2f sa').1)
    (* let (p1, p2) := cf2f sa' in (a * p1 + p2, p1) *)
    | [::] => (1, 0)
    end.

  Compute cf2f [:: 3; 3; 1; 2].             (* (36, 11) *)
  Compute cf2f [:: 0; 1; 1; 1; 1; 1; 1].
  Compute cf2f [:: 1; 2; 2; 2; 2; 2; 2].  

  Lemma num_GaussH s : (cf2f s).1 = GaussH s.
  Admitted.                        (* ssr_cont_fract.v で証明済み。 *)
    
  Lemma num_EulerK s : (cf2f s).1 = EulerK s.
  Proof.
    by rewrite EulerK__GaussH num_GaussH.
  Qed.
  
  Lemma den_GaussH n s : (cf2f (n :: s)).2 = GaussH s.
  Admitted.                        (* ssr_cont_fract.v で証明済み。 *)
  
  Lemma den_EulerK s : 1 <= size s -> (cf2f s).2 = EulerK (↓s).
  Proof.
    move=> Hsize.
    rewrite EulerK__GaussH.
    rewrite -(cons_take_dropE Hsize).
    rewrite den_GaussH.
    done.
  Qed.
  
  Lemma drop_head_rcons s a : 1 <= size s -> ↓(rcons s a) = rcons (↓s) a.
  Proof. by case: s. Qed.
  
(**
最終的に、SBTのノードは連分数である
*)
  Lemma cf_SBK_num_den s : 4 <= size s -> cf2f (rcons s 1) = SBf (SB s).
  Proof.
    move=> Hsize.
    rewrite SBR_num_den //.
    rewrite [cf2f (rcons s 1)]surjective_pairing.
    f_equal.
    - by rewrite num_EulerK.                (* 分子 *)
    - rewrite den_EulerK.
      + rewrite drop_head_rcons //.
          by ssromega.                      (* 0 < size s *)
      + rewrite size_rcons.
          by ssromega.                      (* 0 < (size s).+1 *)
  Qed.
End NUM_DEN.

(**
# （おまけ）SBTのノードが既約になることの証明

SBTのノードに対して $ g $ を次のように定義する。

```math
g (
\begin{pmatrix}
q & v \\
p & u
\end{pmatrix}
)
=
q\ u - p\ v
```

すると、任意のSRBで決まるノード $ N $ について $ g(N) = q\ v - p\ u = 1 $ が成り立つ。

Bezout の補題（拡張ユーグリッドの互除法）から、q と p が互いに素、v と u が互いに素
である。つまり、SBTをたどっていく限り、そのノードはすべて既約分数であるといえる。
 *)
Section COPRIME.
  
  Definition SBg (N : SBNode) : nat := q_ N * u_ N - p_ N * v_ N.

  Lemma SBgI : SBg IDENT = 1.
  Proof. done. Qed.

  Lemma SB_RIGHT q p v u a : ((q, v),
                              (p, u)) * RIGHT a =
                             ((q + a * v, v),
                              (p + a * u, u)).
  Proof. by rewrite mulRa  /q_ /p_ /v_ /u_ /=. Qed.
  
  Lemma SBg_RIGHT N a : SBg (N * RIGHT a) = SBg N.
  Proof.
    case: N => [[q p][v u]].
    rewrite SB_RIGHT /SBg /q_ /p_ /v_ /u_ /=.
    rewrite 2!mulnDl [(a * u * p)%nat]mulnAC subnDr.
    done.
  Qed.
  
  Lemma SB_LEFT q p v u a : ((q, v),
                             (p, u)) * LEFT a =
                            ((q, a * q + v),
                             (p, a * p + u)).
  Proof. by rewrite mulLa  /q_ /p_ /v_ /u_ /=. Qed.
  
  Lemma SBg_LEFT N a : SBg (N * LEFT a) = SBg N.
  Proof.
    case: N => [[q p][v u]].
    rewrite SB_LEFT /SBg /q_ /p_ /v_ /u_ /=.
    rewrite 2!mulnDr.
    rewrite [(a * q)%nat]mulnC.
    rewrite [(v * (q * a))%nat]mulnCA.
    rewrite [(v * a)%nat]mulnC.
    rewrite subnDl.
    done.
  Qed.
  
  Lemma SBcoprime (s : seq nat) : 4 <= size s -> SBg (SB s) = 1.
  Proof.
    move=> HSize.
    apply SB_ind'.
    - move=> a0 a1.
      rewrite /SBg /q_ /p_ /v_ /u_ /=.
      by ssromega.
    - move=> s' Hsize IHs.
      rewrite SBg_LEFT SBg_RIGHT IHs.
      done.
  Qed.
  
End COPRIME.  

(**
# 文献

[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition

[1'] 有澤、安村、萩野、石畑訳、「コンピュータの数学」共立出版


[2.] Stern-Brocot tree

https://en.wikipedia.org/wiki/Stern-Brocot_tree
 *)

(**
# リストのtakeとdrop の別の定義
*)

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

(**
## SBR から ノードへの変換関数

SBR は、

$$ R^{a_0}; L^{a_1}; ...; R^{a_{n-2}}; L^{a_{n-1}} $$

の肩の数字の2個づつのリストとして、つぎのように表記します。

```
[:: (a_0, a_1); ... (a_(n-2), a_(n-1))]
```

SBR からノードへ変換する関数は、次のように定義されます。
先に定義したdropを使用しているため、Function コマンドを使用して、
引数のリストのサイズが減少することを明示的に示す必要があります。

csm_4_4_x_seq_head_last.v で証明した補題 size_belast' を使用しています。
*)  
  Check size_belast'
    : forall (T : eqType) (s : seq T), size (belast' s) = (size s).-1.
  
  Function SB' (s : seq (nat * nat)) {measure size s} : SBNode :=
    match s with
    | [::] => IDENT
    | _ => SB' (s⇓) * RIGHT (s⇑.1) * LEFT (s⇑.2)
    end.
  Proof.
    move=> s a s' H.
    apply/ltP.
    (* see. csm_4_4_x_seq_head_last *)
    rewrite /drop_last size_belast'.
    done.
  Defined.

(**
Functon コマンドによって、関数の定義を簡約する補題が生成されています。
*)  
  Check SB'_equation.
  
  Lemma SB'I : SB' [::] = IDENT.
  Proof.
    (* by rewrite SB'_equation. *)
    done.
  Qed.
  
(**
## 計算例
*)  
  (*                   (R  L)  (R  L) *)
  Compute SBf (SB' [:: (0, 1)]).            (* 1/2 *)
  Compute SBf (SB' [:: (0, 4)]).            (* 1/5 *)
  Compute SBf (SB' [:: (1, 0)]).            (* 2/1 *)
  Compute SBf (SB' [:: (1, 1)]).            (* 3/2 *)
  Compute SBf (SB' [:: (1, 1); (1, 0)]).    (* 5/3 *)
  Compute SBf (SB' [:: (1, 1); (1, 1)]).    (* 8/5 *)
  Compute SBf (SB' [:: (2, 2)]).            (* 7/3 *)  
  
(* END *)
