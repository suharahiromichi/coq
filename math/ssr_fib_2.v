(**
フィボナッチ数列についての定理の証明

フィボナッチ数列と中学入試問題
http://www.suguru.jp/Fibonacci/
*)

From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.
Require Import FunInd.                      (* Functional Scheme *)
Require Import Recdef.                      (* Function *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
ffibonacci
 *)

Section Fib_2.

(**
# fibonacci 関数の定義
*)
  Function fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.
 
  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.

  Lemma fib_1_le_fib2 n : 1 <= fib n.+2.
  Proof.
    elim: n => // n IHn.
    rewrite fib_n.
    rewrite addn_gt0.
    by apply/orP/or_intror.
  Qed.

(**
### 最後の1項を取り出す。

```Σ(i=m..n)f(i) = Σ(i=m..n-1)f(i) + f(n)```

https://staff.aist.go.jp/reynald.affeldt/ssrcoq/bigop_doc.pdf

ただし、f(n)が前に出ていて、見落としてしまう。つぎの p.136 も見よ。

https://staff.aist.go.jp/reynald.affeldt/ssrcoq/ssrcoq.pdf
 *)
  Lemma l_last m n f :
    m <= n ->
    \sum_(m <= i < n.+1)(f i) = \sum_(m <= i < n)(f i) + f n.
  Proof.
    move=> Hmn.
    by rewrite big_nat_recr.
  Qed.

(**
## 性質1（フィボナッチ数列の和）

```Ｆ1 ＋ Ｆ2 ＋ … ＋ Ｆn ＝ Ｆn+2 － 1```

ここでは、帰納法で解く。
 *)
  Lemma lemma1' (n : nat) :
    \sum_(0 <= i < n.+1)(fib i) = fib n.+2 - 1.
  Proof.  
    elim: n => [| n IHn].
    - rewrite big_cons big_nil /=.
      by ssromega.
    - rewrite l_last; last done.
      rewrite IHn.
      rewrite addnBAC; last by rewrite fib_1_le_fib2.
      congr (_ - _).
      by rewrite addnC.
  Qed.

(**
## 性質2（積の和）

```Ｆ1 × Ｆ1 ＋ Ｆ2 × Ｆ2 ＋ … ＋ Ｆn × Ｆn ＝ Ｆn × Ｆn+1```
*)
  Lemma lemma2 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i * fib i) = fib n * fib n.+1.
  Proof.
    elim: n.
    - by rewrite big_cons big_nil /=.
    - move=> n IHn.
      rewrite l_last; last done.
      rewrite IHn.
      rewrite -mulnDl.
      rewrite mulnC.
      by congr (_ * _).
  Qed.

(**
## 性質3 (奇数の和）

```Ｆ1 ＋ Ｆ3 ＋ Ｆ5 ＋ … ＋ Ｆ2n-1 ＝ Ｆ2n```
*)  
  Lemma lemma3 (n : nat) :
    \sum_(0 <= i < n)(fib i.*2.+1) = fib n.*2.
  Proof.
    elim: n.
    - by rewrite big_nil.
    - move=> n IHn.
      have -> : n.+1.*2 = n.*2.+2.
      + rewrite -addn1 -!muln2.
        by ssromega.
      + rewrite fib_n.                      (* 右辺 *)
        rewrite l_last; last done.          (* 左辺 *)
        rewrite IHn.
        by congr (_ + _).
  Qed.

(**
## 性質4（偶数の和）

```Ｆ2 ＋ Ｆ4 ＋ Ｆ6 ＋ … ＋ Ｆ2n ＋ １ ＝ Ｆ2n+1```
*)
  Lemma lemma4 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i.*2) + 1 = fib n.*2.+1.
  Proof.
    elim: n.
    - by rewrite big_cons big_nil /=.
    - move=> n IHn.
      have H : n.+1.*2 = n.*2.+2
        by rewrite -addn1 -!muln2 addn1 2!muln2 doubleS.
      (* 右辺 *)
      rewrite H.
      rewrite !fib_n.
      rewrite -{1}IHn.
      rewrite -addnA.
      rewrite -fib_n.
      rewrite [1 + fib n.*2.+2]addnC.
      
      (* 左辺 *)      
      rewrite l_last; last done.
      rewrite -H -addnA.
      done.
  Qed.

(**
## 性質5（となり同士のフィボナッチ数列は互いに素である。）
 *)
  Lemma lemma5 (n : nat) : coprime (fib n) (fib n.+1).
  Proof.
    rewrite /coprime.
    elim: n => [//= | n IHn].
    rewrite fib_n.
    by rewrite gcdnDr gcdnC.
  Qed.

(**
## 性質6（Ｆn+m ＝ Ｆm × Ｆn+1 ＋ Ｆm-1 × Ｆn）

フィボナッチ数列の加法定理
 *)
  Check fib_ind
    : forall P : nat -> nat -> Prop,
      (forall n : nat, n = 0 -> P 0 0) ->
       (forall n : nat, n = 1 -> P 1 1) ->
       (forall n m : nat,
           n = m.+2 -> P m (fib m) -> P m.+1 (fib m.+1) -> P m.+2 (fib m + fib m.+1)) ->
       forall n : nat, P n (fib n).
  
  Lemma fib_addition' n m :
    fib (n + m.+1) = fib m.+1 * fib n.+1 + fib m * fib n.
  Proof.
    functional induction (fib m).
    - rewrite addn1.
      rewrite [fib 1]/= mul1n mul0n addn0.
      done.
      
    - rewrite addn2.
      rewrite [fib 2]/= add0n 2!mul1n.
      rewrite addnC -fib_n.
      done.
      
    - rewrite fib_n 2!mulnDl.
      
      (* F(n + m.+1) の項をまとめて置き換える *)
      rewrite ?addnA [_ + fib m * fib n]addnC. (* この項を先頭に。 *)
      rewrite ?addnA [_ + fib m.+1 * fib n.+1]addnC ?addnA. (* この項を先頭に。 *)
      rewrite -IHn0.
       
      (* F(n + m.+2) の項をまとめて置き換える *)
      rewrite ?addnA [_ + fib m.+1 * fib n]addnC. (* この項を先頭に。 *)
      rewrite ?addnA [_ + fib m.+2 * fib n.+1]addnC ?addnA. (* この項を先頭に。 *)
      rewrite -IHn1.
      
      rewrite -addn3 addnA addn3.
      rewrite -[m.+2]addn2 addnA addn2.
      rewrite -[m.+1]addn1 addnA addn1.
      rewrite fib_n addnC.
      done.
  Qed.
  
  Lemma fib_addition n m :
    1 <= m -> fib (n + m) = fib m * fib n.+1 + fib m.-1 * fib n.
  Proof.
    move=> H.
    have H' := fib_addition' n m.-1.
    by rewrite prednK in H'.
  Qed.

(**
## 性質7（nがmで割り切れるならば，ＦnはＦmで割り切れる。）

n = qm ならば，ＦnはＦmで割り切れる。
*)
  Lemma lemma7' (m q : nat) : fib m.+1 %| fib (q.+1 * m.+1).
  Proof.
    elim: q => [| q IHq].
    - by rewrite mulSn mul0n addn0.
    - rewrite [q.+2 * m.+1]mulSn.
      rewrite addnC.
      rewrite fib_addition'.
      apply: dvdn_add.
      + by apply: dvdn_mulr.
      + by apply: dvdn_mull.
  Qed.
  
  Lemma lemma7 (m q : nat) : 1 <= m -> 1 <= q -> fib m %| fib (q * m).
  Proof.
    move=> Hm Hq.
    have H' := lemma7' m.-1 q.-1.
    rewrite prednK in H' ; last done.
    rewrite prednK in H' ; last ssromega.
    done.
  Qed.

(**
## 性質8（ＦmとＦm+nの最大公約数 ＝ ＦmとＦnの最大公約数）

```gcd (F m) (F m+n) = gcd (F m) (F n)```
*)
  Lemma lemma8' (m n : nat) :
    gcdn (fib m) (fib (m + n.+1)) = gcdn (fib m) (fib n.+1).
  Proof.
    rewrite fib_addition'.
    rewrite addnC gcdnMDl.
    rewrite Gauss_gcdl; last by rewrite lemma5.
    done.
  Qed.

  Lemma lemma8'' (m n : nat) :
    1 <= n -> gcdn (fib m) (fib (m + n)) = gcdn (fib m) (fib n).
  Proof.
    move=> H.
    rewrite fib_addition; last done.
    rewrite addnC gcdnMDl.
    rewrite Gauss_gcdl; last by rewrite lemma5.
    done.
  Qed.

  Lemma lemma8 (m n : nat) :
    gcdn (fib m) (fib (m + n)) = gcdn (fib m) (fib n).
  Proof.
    case: n => [| n].
    - by rewrite addn0 gcdnn gcdn0.
    - by apply: lemma8''.
  Qed.
  
(**
以下、未整理です。
*)
(**
## 補題9_1（m を n で割ったときのあまりを r とすると，
ＦmとＦnの最大公約数 ＝ ＦnとＦrの最大公約数）
 *)
  Lemma lemma91' (n q r : nat) :
    gcdn (fib (q.+1 * n.+1 + r.+1)) (fib n.+1) = gcdn (fib n.+1) (fib r.+1).
  Proof.
    elim: q => [| q IHq].
    - rewrite mul1n gcdnC.
      rewrite lemma8'.
      done.
    - rewrite gcdnC mulSn addnC -?addnA addnCA.
      rewrite lemma8.
      by rewrite gcdnC addnC.
  Qed.
  
  Lemma lemma91'' (n q r : nat) :
    gcdn (fib (q.+1 * n + r.+1)) (fib n) = gcdn (fib n) (fib r.+1).
  Proof.
    elim: q => [| q IHq].
    - by rewrite mul1n gcdnC lemma8'.
    - rewrite gcdnC mulSn addnC -?addnA addnCA.
      rewrite lemma8.
      by rewrite gcdnC addnC.
  Qed.
  
  Lemma lemma91''' (n q r : nat) :
    gcdn (fib (q * n + r.+1)) (fib n) = gcdn (fib n) (fib r.+1).
  Proof.
    elim: q => [| q IHq].
    - by rewrite gcdnC mul0n add0n.
    - rewrite gcdnC mulSn addnC -?addnA addnCA.
      rewrite lemma8.
      by rewrite gcdnC addnC.
  Qed.

  Lemma lemma91_r1 (n q r : nat) :
    1 <= r ->
    gcdn (fib (q * n + r)) (fib n) = gcdn (fib n) (fib r).
  Proof.
    move=> H.
    have H' := lemma91''' n q r.-1.
    by rewrite prednK in H'.
  Qed.

  (* r = 0 の特別な場合は、性質7である。 *)
  Lemma lemma91_r0 (n q : nat) :
    1 <= n ->
    1 <= q ->
    gcdn (fib (q * n)) (fib n) = gcdn (fib n) (fib 0).
  Proof.
    move=> Hn Hq.
    rewrite [fib 0]/= gcdn0.
    apply/gcdn_idPr.
    by apply/lemma7.
  Qed.

  Lemma lemma91 (n q r : nat) :
    1 <= n ->
    1 <= q ->
    gcdn (fib (q * n + r)) (fib n) = gcdn (fib n) (fib r).
  Proof.  
    move=> Hn Hq.
    case Hr : (r == 0).
    - move/eqP in Hr.
      rewrite Hr addn0.
      by apply: lemma91_r0.
    - move/eqP in Hr.
      move/PeanoNat.Nat.neq_0_lt_0 in Hr.
      move/ltP in Hr.
      by rewrite lemma91_r1.
  Qed.
  
 Lemma lemma912 (m n : nat) :
   1 <= m ->
   1 <= n ->
   n <= m ->
   gcdn (fib m) (fib n) = gcdn (fib n) (fib (m %% n)).
 Proof.
   move=> Hm Hn Hnm.
   have Hq : 1 <= m %/ n by rewrite divn_gt0.
   have H := @lemma91 n (m %/ n) (m %%n) Hn Hq.
   by rewrite -divn_eq in H.
 Qed.
 
(**
## 性質9（ＦmとＦnの最大公約数 ＝ Ｆ(mとnの最大公約数)）

```gcd (F m) (F n) = F (gcd m n)```
*)
 Lemma lemma9 (m n : nat) :
   gcdn (fib m) (fib n) = fib (gcdn m n).
 Proof.
   (* see. ssr_fib_3.v または ssr_fib_3_2.v *)
 Admitted.                                  (* OK *)

(**
## 性質10（Ｆn が Ｆm で割り切れるならば，nはmで割り切れる。）

性質7の逆
*)
 Lemma fib_0 n : fib n = 0 -> n = 0.
 Proof.
   functional induction (fib n) => //.
   rewrite -fib_n.
 Admitted.
 
 Lemma fib_ge_2 n m : 1 < gcdn n.+2 m.
 Proof.
 Admitted.

 (* F_n が単射なのは、2からである。 *)
 Lemma fib_inj n1 n2 : 1 < n1 -> fib n1 = fib n2 -> n1 = n2. (* injective fib. *)
 Proof.
   move: n2.
   functional induction (fib n1) => //.
   rewrite -fib_n.
   move=> n2.
 Admitted.
 
 Lemma lemma10 (m n : nat) : fib n %| fib m -> n %| m.
 Proof.
   case: n.
   - rewrite [fib 0]/fib.
     rewrite 2!dvd0n.
     move/eqP => H.
     apply/eqP.
     by apply: fib_0.
   - case=> n.
     + by apply: dvd1n.
     + move/gcdn_idPl.
       rewrite lemma9.
       move/fib_inj => H.
       apply/gcdn_idPl.
       rewrite H //.
       by apply: fib_ge_2.
 Qed.
 
End Fib_2.

(* END *)
