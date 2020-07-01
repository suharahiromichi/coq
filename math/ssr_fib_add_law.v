(**
フィボナッチ数列の加法定理
========================

@suharahiromichi

2020/07/01
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import FunInd.                      (* Functional Scheme *)
Require Import Recdef.                      (* Function *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

フィボナッチ ffibonacci 数列には、加法定理 addition theorem
(加法法則 addition law) が成り立ちます。 $ 1 \le m$ のとき、

$$ F_(n + m) = F_m F_(n+1) + F_(m-1) F_n $$

フィボナッチ数列の定義は、だれでも知っている単純なものですが、
1個前と2個前の項を参照する、という意味で、帰納法としては複雑なかたちをしています。

そこで、Coqの「特定の再帰関数に専用の帰納法」のための
コマンド ``functional induction`` を使って解いてみましょう。
 *)

Section Fib_2.

(**
# fibonacci 関数の定義

``functional induction`` を使うためには、
関数を``Fixpoint``ではなく、``Function``で定義する必要があります。
*)
  Function fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.

(**
``Function``コマンドをで定義すると、``functional induction``を行うための``fib_ind``が定義されます。
 *)
  Check fib_ind
    : forall P : nat -> nat -> Prop,
      (forall m : nat, m = 0 -> P 0 0) ->
      (forall m : nat, m = 1 -> P 1 1) ->
      (forall m k : nat,
          m = k.+2 -> P k (fib k) -> P k.+1 (fib k.+1) -> P k.+2 (fib k + fib k.+1)) ->
      forall m : nat, P m (fib m).


(**  
簡単にいうと、命題 P(m, F_m) に対して、次の帰納法で証明することができます。

- 命題が、P(0, F_0) で成り立つ場合を証明する。F_0 = 0 なので P(0, 0)
- 命題が、P(1, F_1) で成り立つ場合を証明する。F_1 = 1 なので P(1, 1)
- 命題が、P(k, F_k) と P(m=k+1, F_k+1) で成り立つと仮定して、P(m=k+2, F_k + F_k+1)
で成り立つこと証明する。
- 以上から、命題は、任意の P(m, F_m) で成り立つ。

つまり、フィボナッチ数列の定義そのものですね。
*)  
  
(**
また、関数の展開をするための``fib_equation``が定義されます。
 *)
  Check fib_equation
    : forall n : nat,
      fib n = match n with
              | 0 => 0
              | 1 => 1
              | (m.+1 as pn).+1 => fib m + fib pn
              end.


(**  
``Function`` で関数を定義すると、
関数を展開するunfoldタクティクが、事実上、使用不能になるため、
代わりに ``rewrite fib_equation`` による書き換えを可能にするためのものです。
なお、今回は使用しません。
*)  

(**
# 補題

定義から導かれる、簡単な補題を証明しておきます。
*)  
  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.

(**
# フィボナッチ数列の加法定理

最初にCoqで扱い易い、引き算の無いかたちで証明します。
この場合 n、m とも任意の自然数でよいです。

$$ F_(n + m + 1) = F_(m + 1) F_(n+1) + F_m F_n $$
 *)
  Lemma fib_addition' n m :
    fib (n + m.+1) = fib m.+1 * fib n.+1 + fib m * fib n.
  Proof.
(**
F_m に対する帰納法をおおこなう。mだけの帰納法ではない。
*)
    functional induction (fib m).

(**
- P(m=0, F_0) を証明する。
*)
    - rewrite addn1.
      rewrite [fib 1]/= mul1n mul0n addn0.
      done.
      
(**
- P(m=1, F_1) を証明する。
*)
    - rewrite addn2.
      rewrite [fib 2]/= add0n 2!mul1n.
      rewrite addnC -fib_n.
      done.
      
(**
- IHn0 : P(m=m, F_m) で成り立つ。
- IHn1 : P(m=m+1, F_m+1) で成り立つ。
- Goal : P(m=m+2, F_m + F_m+1) で成り立つことを証明する。

前節での説明上の k が、ここでは m になっています。
*)
    - rewrite fib_n 2!mulnDl.
      
      (* F_(n + m.+1) の項をまとめて置き換える *)
      rewrite ?addnA [_ + fib m * fib n]addnC. (* この項を先頭に。 *)
      rewrite ?addnA [_ + fib m.+1 * fib n.+1]addnC ?addnA. (* この項を先頭に。 *)
      rewrite -IHn0.
       
      (* F_(n + m.+2) の項をまとめて置き換える *)
      rewrite ?addnA [_ + fib m.+1 * fib n]addnC. (* この項を先頭に。 *)
      rewrite ?addnA [_ + fib m.+2 * fib n.+1]addnC ?addnA. (* この項を先頭に。 *)
      rewrite -IHn1.
      
      have -> : n + m.+3 = (m + n).+3 by ssromega.
      have -> : n + m.+2 = (m + n).+2 by ssromega.
      have -> : n + m.+1 = (m + n).+1 by ssromega.
      rewrite fib_n.
      rewrite [fib (m + n).+2 + fib (m + n).+1]addnC.
      done.
  Qed.

(**
最後に、$1 \le m$ の条件のもとで、定理を証明します。

$$ F_(n + m) = F_m F_(n+1) + F_(m-1) F_n $$
*)  
  Lemma fib_addition n m :
    1 <= m -> fib (n + m) = fib m * fib n.+1 + fib m.-1 * fib n.
  Proof.
    move=> H.
    have H' := fib_addition' n m.-1.
      by rewrite prednK in H'.
  Qed.

(**
``n - 1 + 1 = n`` をいうためには、``0 < n`` の条件が必要です。
これは、n が自然数の0のとき、``0 - 1 = 0`` となるためです。
*)

  Check prednK : forall n : nat, 0 < n -> n.-1.+1 = n.

End Fib_2.

(* END *)
