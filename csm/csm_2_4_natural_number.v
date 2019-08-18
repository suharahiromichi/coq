From mathcomp Require Import all_ssreflect. (* ssrnat を含む。 *)
(**

# テキストの解読

## addOnEqn の証明

### 6行目

- nat        の定義
- 0   (O)    の定義
- +   (addn) の定義
- .+1 (S)    の定義
- =   (eq)   の定義

- a = b が成り立つとは、それが定義から証明できるということ（同じに見える、ともいう）。
Trueを返すという言い方は間違いである。True（常に証明可能）と同値というべき。

C-H対応のことだとしても、P : a = b なるPは、その証明を返す。

定理証明器では、証明可能であることは判っても、真であることは判らない。
（証明不能であることも判らない）
前提に矛盾があれば（不健全なら）、偽な命題も証明できる。
ただし、公理なし証明器であるCoqでは、その危険は少ない。

（補足） a == b （= ふたつ）が成り立つとき true（bool値、小文字）を返す。
この両者は違う概念だが、それらが同値であるならば、相互変換できる（リフレクション）。

### 7行目

## addn3Eq2n1 の証明

### 9行目

### 11行目

- rewite タクティク、= (eq) で置き換える。
- addn1 補題

### 12行目

- add2n 補題

### 13行目

- addnC 補題

### 14行目      

## sumGauss の証明

### 17行目

- sum の定義をする。

### 19行目

- muln の定義

### 21行目

- elim タクティク

  elim: n => [// | n IHn]
  は、
  move: n.
  elim.
    - move=> //.       (* rewrite // または try done *)
    - move=> n IHn.
  とおなじ。move と : と => は、前回までの復習。

### 22行目

- mulnC 補題

### 23行目

- rewrite ( _ : a = b) (バニラCoqの replace タクティク)

- last first タクティク

### 24行目 (a = bの証明)

### 25行目 (a = bの証明)

### 26行目

- mulnDr

### 27行目

- rewrite ... in ... タクティク

### 28行目

- 帰納法の仮定 (IH) で rewrite する。

### 29行目

- 数!rewrite タクティク

### 30行目

- [...]rewrite タクティク

### 31行目

- mulnDl 補題

- -rewrite タクティク

### 32行目

- (補足) sumGauss によって、sum n * 2 と (n + 1) * n が同じに見えることが証明できた。
以降、rewrite sumGauss での書き換えができるようになる。

   *)

Section naturalNumber.

  Lemma add0nEqn (n : nat) : 0 + n = n.
  Proof.
    rewrite add0n.
    (* n = n *)
    done.
  Qed.
  
  Lemma addn3Eq2n1 (n : nat) : n + 3 = 2 + n + 1.
  Proof.
    Check (addn1 (2 + n)).
    rewrite addn1.
    rewrite add2n.
    rewrite addnC.
    rewrite add3n.                          (* テキストにはない。 *)
      (* n.+3 = n.+3 *)
      by [].
  Qed.
  
  Fixpoint sum (n : nat) := if n is m.+1 then sum m + n else 0.

  (* テキストの例 *)

  Lemma sumGauss (n : nat) : sum n * 2 = (n + 1) * n.
  Proof.
    elim: n => [// | n IHn].
    rewrite mulnC.
    rewrite (_ : sum n.+1 = n.+1 + (sum n)); last first.
    - rewrite /=.
      rewrite addnC.
      done.
    - rewrite mulnDr.
      rewrite mulnC in IHn.
      rewrite IHn.
      rewrite 2!addn1.
      rewrite [_ * n]mulnC.
      rewrite -mulnDl.
      rewrite add2n.                        (* テキストでは省略 *)
        (* n.+2 * n.+1 = n.+2 * n.+1 *)
        by [].
  Qed.
  
  (* 例2. 再帰呼び出しの1回分（と加算の可換）を補題にする。 *)
  
  Lemma l_sum' (n : nat) : sum n.+1 = n.+1 + sum n.
  Proof.
    rewrite /=.                      (* simpl で sum の計算をする。 *)
      by rewrite addnC.
  Qed.

  Lemma sumGauss'''' (n : nat) : sum n * 2 = (n + 1) * n.
  Proof.
    (* Mathcomp の復習。 *)
    move: n.                  (* 帰納法を使う対象をgeneralizeする。 *)
    elim.                     (* スタックトップに対して、帰納法を使う。 *)
    (* 場合分けする。*)
    (* 帰納法の底 *)
    - simpl. (* sum 0 を計算する。足し算(+)を計算しているわけではないことに注意！ *)
      reflexivity.
    (* 帰納法の仮定を intro する。 *)
    - move=> n IHn.
      rewrite mulnC in IHn.
      rewrite mulnC l_sum' mulnDr IHn.
        by rewrite 2!addn1 [_ * n]mulnC -mulnDl add2n. (* ring *)
  Qed.
  
  Lemma sumGauss' (n : nat) : sum n * 2 = (n + 1) * n.
  Proof.
    elim: n => [// | n IHn].
    rewrite mulnC in IHn.
      by rewrite mulnC l_sum' mulnDr IHn 2!addn1 [_ * n]mulnC -mulnDl add2n.
  Qed.
  
  (* 例3. 再帰呼び出しの1回分を補題にする。 *)
  
  Lemma l_sum'' (n : nat) : sum n.+1 = sum n + n.+1.
  Proof.
    by rewrite /=.
  Qed.

  Lemma sumGauss'' (n : nat) : sum n * 2 = (n + 1) * n.
  Proof.
    elim: n => [// | n IHn].
    rewrite mulnC in IHn.
      by rewrite mulnC l_sum'' addnC mulnDr IHn 2!addn1 [_ * n]mulnC -mulnDl add2n.
  Qed.
  
  (* 例4. ring を使う。  *)
  
  Lemma sumGauss''' (n : nat) : sum n * 2 = (n + 1) * n.
  Proof.
    elim: n => [// | n IHn].
    rewrite mulnC in IHn.
    rewrite mulnC l_sum'' addnC mulnDr IHn.
    (* 帰納法の仮定を適用し、sum が消える。 *)
    ring.
  Qed.
  
End naturalNumber.

(* END *)
