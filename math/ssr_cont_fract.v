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
# 連分数 Continued fraction

有限単純連分数 または 有限正則連分数 (finite regular continued fraction)
これは、分子が全て 1 の連分数で、有限回で表現できるもの。有理数を表す。

また、ここでは、正数のみ考えるが、1以上であってもよい。
 *)
Section CF.

(**
## （正の）有理数と有限正則連分数 の相互変換

-（正の）有理数は、自然数のpairで表現する。既約である必要はない。
- 有限正則連分数は、自然数のリストで表現する。
*)

(**
### 正則連分数から有理数

得られた有理数は、結果として既約になる。証明が必要か？
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
  
(**
### 有理数から正則連分数
*)
  Program Fixpoint f2cf'p (n m : nat) {wf lt m} : (seq nat) := (* notu *)
    match m with
    | 0 => [::]
    | _ => (n %/ m) :: f2cf'p m (n %% m)
    end.
  Obligation 1.
  Proof.
    apply/ltP/ltn_pmod.
    move/Lt.neq_0_lt in H.
    apply/ltP/H.
  Qed.
  Compute f2cf'p 36 11.                     (* [:: 3; 3; 1; 2] *)
  
  Function f2cf' (n m : nat) {wf lt m} : (seq nat) :=
    match m with
    | 0 => [::]
    | _ => (n %/ m) :: f2cf' m (n %% m)
    end.
  Proof.
    - move=> n m m0 _.
      apply/ltP.
        by rewrite ltn_mod.
    - by apply: lt_wf.
  Defined.                                (* Defined が必要である。 *)
(**
- Coq は停止性が判定できないので、Function コマンドを使う。
第2引数（分母側）が、割り算の余りを求めることによって小さくなることを示す。

- Function コマンドにより、カスタムインダクションが可能になる
(functional inducntion タクティクが使えるようになる）。

- Function コマンドにより、不動点を示す等式 f2cf'_equation が定義される。
 *)
  
  Definition f2cf (p : (nat * nat)) : (seq nat) := f2cf' p.1 p.2.
  Compute f2cf (36, 11).                    (* = [:: 3; 3; 1; 2] *)
  
  Compute cf2f (f2cf (36, 11)).             (* (36, 11) *)
  Compute cf2f (f2cf (72, 22)).             (* (36, 11) *)
  

(**
## 有理数→正則連分数→有理数 の変換
*)
  Goal forall p, cf2f (f2cf p) = p.
  Proof.
    case=> n m.
    functional induction (f2cf' n m).
    - rewrite /=.
      (* (1, 0) = (n, 0) .... p は既約になるので。 *)
      admit.
    - case: m y IHl => [H IHl | m H IHl].
      + done.
      + admit.
(**
  IHl : cf2f (f2cf (m.+1, n %% m.+1)) = (m.+1, n %% m.+1)
  ============================
  cf2f (f2cf (n, m.+1)) = (n, m.+1)
 *)
  Admitted.                                 (* OK *)

(**
## 正則連分数→有理数→正則連分数 の変換

cf2f (f2cf p) = p は証明できない（pが約分される）ので、
f2cf (cf2f s) = s を証明する。
*)  
  Lemma f2cfE (n m : nat) : m != 0 -> f2cf' n m = (n %/ m) :: f2cf' m (n %% m).
  Proof.
    case: m.
    - done.
    - move=> n' Hm.
      apply: f2cf'_equation.
  Qed.
  
  Lemma div_m__n n m r : 0 < m -> r < m -> (n * m + r) %/ m = n.
  Proof.
    move=> Hm Hrm.
    rewrite divnMDl; last done.
    rewrite divn_small; last done.
      by rewrite addn0.
  Qed.
  
  Lemma mod_m__r n m r : r < m -> (n * m + r) %% m = r.
  Proof.
    move=> Hrm.
    Check modnMDl.                     (* (p * d + m) %% d = m %% d *)
    rewrite modnMDl.
    rewrite modn_small; last done.
    done.
  Qed.
  
  Goal forall s, f2cf (cf2f s) = s.
  Proof.
    elim => // n s IHs /=.
    rewrite /f2cf /=.
    - rewrite f2cfE /=.
      + rewrite div_m__n.
        * rewrite mod_m__r.
          -- rewrite /f2cf in IHs.
               by rewrite IHs.
          -- admit.                      (* (cf2f s).2 < (cf2f s).1 *)
        * admit.                         (* 0 < (cf2f s).1 *)
        * admit.                         (* (cf2f s).2 < (cf2f s).1 *)
    - admit.                             (* (cf2f s).1 != 0 *)  
  Admitted.
  
End CF.

(**
# continuant polynomial

文献[1] では Gauss が定義してものとして、H(・) と表記されている。
リストの前に追加する。consによる定義。

文献[2] では、Eulerが研究したものとして、 K(・) と表記されている。
リストの後に追加する。rconsによる定義。
 *)
Section CP.

(**
## Gauss の H関数

### Gauss の H関数の定義

```
H() = 1
H(x_1) = x_1
H(x_1 ... x_n) = x_1 * K(x_2 ... x_n) + K(x_3 ... x_n)
```
*)
  Program Fixpoint GaussHp (s : seq nat) {measure (size s)} : nat := (* notu *)
    match s with
    | [::] => 1
    | [:: n] => n
    | n0 :: n1 :: s' => n0 * GaussHp (n1 :: s') + GaussHp s'
    end.
  Obligation 2.
  Proof.
    apply/ltP => /=.
    (* size s' < (size s').+2 *)
      by ssromega.
  Qed.

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
  Compute cf2f [:: 3; 3; 1; 2].             (* (36, 11) *)
  
(**
### 連分数とcontinuant

有限正則連分数 s が、有理数 ``n / d`` を示すとする。

- H(s)は、有理数の分子 n である。
- H(behead s)は、有理数の分母 d である。

```n / d = H(x1 x2 x3 ... ) / H(x2 x3 ...) = [x1; x2, x3 ...]```
のように表される（文献 [3]）。
*)
  Lemma cf2fE n0 n1 s :
    (cf2f [:: n0, n1 & s]).1 = n0 * (cf2f (n1 :: s)).1 + (cf2f s).1.
  Proof.
    done.
  Qed.
  
  Goal forall s, (cf2f s).1 = GaussH s.
  Proof.
    move=> s.
    functional induction (GaussH s).
    - done.
    - by rewrite /cf2f muln1 addn0.
    - rewrite -IHn -IHn0.
      rewrite -cf2fE.
      done.
  Qed.
  
  Goal forall n s, (cf2f (n :: s)).2 = GaussH s.
  Proof.
    move=> n s.
    functional induction (GaussH s).
    - done.
    - by rewrite /cf2f muln1 addn0.
    - rewrite -IHn0 -IHn1.
      rewrite -cf2fE.
      done.
  Qed.
  
(**
### continuant の性質
*)

  Compute GaussH [:: 1;2;3;4;5].                       (* 225 *)
  Compute GaussH [:: 5;4;3;2;1].                       (* 225 *)
  Compute 5 * GaussH [:: 1;2;3;4] + GaussH [:: 1;2;3]. (* 225 *)

  Compute (GaussH [:: 1;2;3] * GaussH [:: 4;5]) + (GaussH [:: 1;2] * GaussH [:: 5]).
  (* 225 *)

  Lemma GaussHE (n0 n1 : nat) (s : seq nat) :
    GaussH (n0 :: n1 :: s) = n0 * GaussH (n1 :: s) + GaussH s.
  Proof.
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
      rewrite [n2 * (n0 * GaussH (n3 :: rcons s' n1))]mulnCA.
        by ssromega.
  Qed.
  
  Lemma GaussH__GaussH_rev s : GaussH s = GaussH (rev s).
  Proof.
    functional induction (GaussH s) => //=.
    rewrite !rev_cons.
    rewrite GaussHEr.
    rewrite -rev_cons.
    rewrite IHn IHn0.
    done.
  Qed.

(**
## Euler の K関数

### Euler の K関数の定義

```
K() = 1
K(x_1) = x_1
K(x_1 ... x_n) = K(x_1 ... x_n-1) * x_n + K(x_1 ... x_n-2)
```
*)

(*
  Fixpoint tail (s : seq nat) : nat :=
    match s with
    | [::] => 0
    | [:: a] => a
    | a :: s => tail s
    end.
  
  Fixpoint body (s : seq nat) : seq nat :=
    match s with
    | [::] => [::]
    | [:: a] => [::]
    | a :: s => a :: body s
    end.
 *)
  Definition tail (s : seq nat) : nat := head 0 (rev s).
  Compute tail [:: 1; 2; 3].                (* 3 *)

  Definition body (s : seq nat) : seq nat := rev (drop 1 (rev s)).
  Compute body [:: 1; 2; 3].                (* [:: 1; 2] *)
  
  Lemma tail_rcons s n : tail (rcons s n) = n.
  Proof.
      by rewrite /tail rev_rcons.
  Qed.
  
  Lemma body_rcons s n : body (rcons s n) = s.
  Proof.
      by rewrite /body rev_rcons /= drop0 revK.
  Qed.
  
  Lemma size_body_1 s : 1 <= size s -> size (body s) < size s.
  Proof.
    case/lastP : s => // s n Hs.
    rewrite body_rcons size_rcons.
    done.
  Qed.
  
  Lemma size_body_21 s : 2 <= size s -> size (body (body s)) < size (body s).
  Proof.
    case/lastP : s => // s n Hs.
    rewrite body_rcons.
    apply: size_body_1.
    rewrite size_rcons in Hs.
      by ssromega.
  Qed.
  
  Lemma size_body_2 s : 2 <= size s -> size (body (body s)) < size s.
  Proof.
    move=> Hs.
    Check @ltn_trans (size (body s)) (size (body (body s))) (size s).
    apply: (@ltn_trans (size (body s)) (size (body (body s))) (size s)).
    - by apply: (@size_body_21 s).
    - apply: size_body_1.
        by ssromega.
  Qed.
  
  Lemma tail_rev n s : tail (rev (n :: s)) = n.
  Proof.
    rewrite rev_cons.
      by rewrite tail_rcons.
  Qed.
  
  Lemma body_rev n s : body (rev (n :: s)) = rev s.
  Proof.
    rewrite rev_cons.
      by rewrite body_rcons.
  Qed.
  
  Function EulerK (s : seq nat) {measure size s} : nat :=
    match s with
    | [::] => 1
    | [:: n] => n
    | _ => tail s * EulerK (body s) + EulerK (body (body s))
    end.
  - move=> s n s' n' s'' H1 H2.
    apply/ltP.
    Check @size_body_2 [:: n, n' & s''].
    apply: (@size_body_2 [:: n, n' & s'']).
    done.
  - move=> s n s' n' s'' H1 H2.
    apply/ltP.
    Check @size_body_1 [:: n, n' & s''].
    apply: (@size_body_1 [:: n, n' & s'']).
    done.
  Defined.
  
  Compute EulerK  [:: 3; 3; 1; 2].          (* 36 *)
  Compute EulerK  [:: 3; 1; 2].             (* 11 *)

(**
### EulerK と GaussH が同じ
*)  
  Lemma EulerKE s :
    2 <= size s ->
    EulerK s = tail s * EulerK (body s) + EulerK (body (body s)).
  Proof.
    case: s.
    - done.
    - move=> n0 s.
      case: s.
      + done.
      + move=> n1 s Hs.
        by rewrite EulerK_equation.
  Qed.
  
  Lemma EulerK_rev__GaussH s : EulerK (rev s) = GaussH s.
  Proof.
    functional induction (GaussH s).
    - done.
    - done.
    - rewrite EulerKE.
      + rewrite tail_rev 2!body_rev.
        rewrite IHn -IHn0.
        done.
      + rewrite size_rev.
        by rewrite /=.
  Qed.
  
  Lemma EulerK_GaussH s : EulerK s = GaussH s.
  Proof.
    rewrite -(revK s).
    rewrite EulerK_rev__GaussH GaussH__GaussH_rev.
    rewrite revK.
    done.
  Qed.
  
(**
# 連分数とフィボナッチ数（と黄金数）

```n/d = (a2 / a1) = 3/2 = H(1, 1, 1) / H(1, 1) = [1; 1, 1] = (fib 4 / fib 3)```

``(a_n / a_n-1) = [1をn個] = H(1をn個)/H(1をn-1個) = (fib n+1 / fib n)```

文献[4]。このことから、1をn個の連分数は、``fib n.+1`` に等しい。

- H(1; 1; 1) = fib 4
- H(nseq n 1) = fib n.+1
*)
  Compute GaussH [::].                      (*      1 = fib 1 *)
  Compute GaussH [:: 1].                    (* a0 = 1 = fib 2 *)
  Compute GaussH [:: 1; 1].                 (* a1 = 2 = fib 3 *)
  Compute GaussH [:: 1; 1; 1].              (* a2 = 3 = fib 4 *)
  Compute GaussH (nseq 3 1).

  Function fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.
  
  Lemma fibE n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.
  
  Goal forall n, GaussH (nseq n 1) = fib n.+1.
  Proof.
    move=> n.
    functional induction (fib n) => [//= | //= |].
    rewrite fibE -IHn0 -IHn1.
    rewrite [nseq _.+2 1]/=.
    rewrite GaussHE mul1n.
    rewrite [nseq _.+1 1]/=.
      by rewrite addnC.
  Qed.

(**
（参考）フィボナッチ数列の隣接2項の商は、黄金数φに収束する。  
*)

End CP.

(**
# 文献

[1] 有澤健治、平方根の連分数とペル方程式, 第1章
https://leo.aichi-u.ac.jp/~keisoken/research/books/book51/book51.pdf


[2] Ronald L. Graham, Donald E. Knuth, Oren Patashnik, Concrete Mathematics,
6.7 CONTINUANTS


[3] Wikipedia, Continuant (mathematics), 
https://en.wikipedia.org/wiki/Continuant_(mathematics)
Properties 「Ratios of continuants represent (convergents to) 
continued fractions as follows:」

[4] Wikipedia, 連分数
https://ja.wikipedia.org/wiki/連分数
連分数の性質「なお数列an が全て 1 の場合、数列pn, qn はともにフィボナッチ数列 
(F0 = 0, F1 = 1) である」
 *)

(* END *)
