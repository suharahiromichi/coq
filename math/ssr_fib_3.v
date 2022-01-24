(**
フィボナッチ数の最大公約数 (GCD of Fibonacci Numbers)
============================

@suharahiromichi

2022/01/21
*)

(**
このソースは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_fib_3.v
*)

(**
# はじめに

m番めとn番めフィボナッチ数の最大公約数は、mとnの最大公約数番めのフィボナッチ数に等しい、
という定理があります。

```math
gcd(F_m, F_n) = F_{gcd(m, n)}

```

これは エドゥアール・リュカ (ルーカス）が最初に報告したのを
クヌース先生が紹介して広まったのだそうです。
TAOCP[2]に掲載されているようですが、私が読んだのは [1]と[1'] のほうで、
証明は演習問題(6.27)になっています。

そこでで、早速答えをみると(w)、
フィボナッチ数の加法定理に相当する式から、「$ m > n $ 
ならば、$ gcd(F_m, F_n) = gcd(F_{m - n}, F_n) $
であることに注意して、帰納法使って証明せよ」、とだけ書いてあります。

証明を集めたサイト[3]を見ても書いてあることは同じで、[4]
はもう少し詳しいですが、帰納法のところは証明というより説明になっています。

では、この定理の証明をCoqでやってみましょう、とりあえず、以下の方針でおこないます。

1. gcdに関する帰納法が肝なので、そこは Coq の Functional Induction [5] に任せる。

2. 1.のためには、Function コマンドで自分でフィボナッチ数を定義する必要がある。
それも [5] を参考にした。

3. MathComp の GCDに関する豊富な補題を使うために、2.の定義と
MathCompのGCDの定義が同じであることを証明しておく。



MathCompで証明をするならば、MathCompで定義されている
自然数の最大公約数の関数 gcdn について、なんらかのかたちで帰納法の原理を用意するのが
正しいアプローチですが、それはまだできていません。

また、フィボナッチ数の加法定理については、[6] で証明しているため、証明は省略します。
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import FunInd.                      (* Functional Scheme *)
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Fib3.

(**  
# フィボナッチ数の定義と定理
*)
  Function fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.
  
(**
1個分フィボナッチ数の計算
 *)
  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.

(**
隣り合ったフィボナッチ数は互いに素である。
*)
  Lemma fib_coprime (n : nat) : coprime (fib n) (fib n.+1).
  Proof.
    rewrite /coprime.
    elim: n => [//= | n IHn].
    rewrite fib_n.
      by rewrite gcdnDr gcdnC.
  Qed.
  
(**
フィボナッチ数列の加法定理
*)
  Lemma fib_addition n m :
    1 <= m -> fib (n + m) = fib m * fib n.+1 + fib m.-1 * fib n.
  Proof.
    (* see. ssr_fib_2.v *)
  Admitted.                                 (* OK *)

(**
# GCDの定義と定理
*)  
(**
Function を使って自分で定義する。
*)
  Function gcd (m n : nat) {wf lt m} : nat :=
    match m with
    | 0 => n
    | _ => gcd (n %% m) m
    end.
  Proof.
    - move=> m n m0 _.
      apply/ltP.
        by rewrite ltn_mod.
    - by apply: lt_wf.
  Qed.

(**
MathComp の gcdn を同じであることを証明する。
*)  
  Lemma gcdE m n : gcdn m n = gcd m n.
  Proof.
    functional induction (gcd m n).
    - by rewrite gcd0n.
    - rewrite -IHn0.
        by rewrite gcdnC gcdn_modl.
  Qed.
  
(**
GCDの可換性
*)
  Check gcdnC : forall m n, gcdn m n = gcdn n m.
  Lemma gcdC m n : gcd m n = gcd n m.
  Proof.
      by rewrite -2!gcdE gcdnC.
  Qed.

(**
GCDの簡単な性質
*)  
  Lemma gcd0m m : gcd 0 m = m.
  Proof.
      by rewrite gcd_equation.            (* gcd の定義で展開する。 *)
  Qed.
  
  Lemma gcdmm m : gcd m m = m.
  Proof.
    case: m => [| m].
    - by rewrite gcd_equation.
    - by rewrite gcd_equation modnn gcd0m.
  Qed.
  
  Lemma gcdnn_gcd0n n : gcd n n = gcd 0 n.
  Proof.
      by rewrite gcdmm gcd0m.
  Qed.
  
  Check gcdnMDl : forall k m n : nat, gcdn m (k * m + n) = gcdn m n.
  Lemma gcdMDl (k m n : nat) : gcd m (k * m + n) = gcd m n.
  Proof.
      by rewrite -2!gcdE gcdnMDl.
  Qed.
  
  Check Gauss_gcdl : forall p m n : nat, coprime p n -> gcdn p (m * n) = gcdn p m.
  Lemma Gauss_gcdl' p m n : coprime p n -> gcd p (m * n) = gcd p m.
  Proof.
    rewrite -2!gcdE.
      by apply: Gauss_gcdl.
  Qed.
  
(**
# フィボナッチ数のGCD
*)

(**
GKPの解答にある、``m > n`` ならば ``gcd (fib m) (fib n) = gcd (fib (m - n)) (fib n)``
と同じものを証明するが、そのために ``m`` を ``0`` と非0で振り分ける。
 *)
  Lemma fib_lemma_gkp' m n :
    1 <= m -> gcd (fib (n + m)) (fib n) = gcd (fib m) (fib n).
  Proof.
    move=> H.
    rewrite fib_addition //.
    rewrite gcdC addnC gcdMDl.
    rewrite Gauss_gcdl'.
    - by rewrite gcdC.
    - by apply: fib_coprime.
  Qed.
  
  Lemma fib_lemma_gkp m n :
    gcd (fib (n + m)) (fib n) = gcd (fib m) (fib n).
  Proof.
    case: m => [| m].
    - rewrite addn0 /=.
        by apply: gcdnn_gcd0n.
    - rewrite fib_lemma_gkp' //=.
  Qed.
  
(**
gcdnMDl のフィボナッチ数版
*)
  Check gcdnMDl : forall k m n : nat, gcdn m (k * m + n) = gcdn m n.
  Lemma fib_gcdMDl n q r :
    gcd (fib (q * n + r)) (fib n) = gcd (fib n) (fib r).
  Proof.
    elim: q => [| q IHq].
    - rewrite mul0n add0n.
      rewrite gcdC.
      done.
    - Search _ (_.+1 * _).
      rewrite mulSn -addnA.
      rewrite [LHS]fib_lemma_gkp.
      done.
  Qed.
  
(**
gcdn_modr のフィボナッチ数版
*)
  Check gcdn_modr : forall m n : nat, gcdn m (n %% m) = gcdn m n.
  Lemma fin_gcd_modr m n :
    gcd (fib m) (fib n) = gcd (fib n) (fib (m %% n)).
  Proof.
    move: (fib_gcdMDl n (m %/ n) (m %% n)).
    rewrite -divn_eq.
    done.
  Qed.

(**
# 証明したいもの

$ F_0 = 0 $ や $ F_1 = 1 $ でも成り立つことを確認しておく。
*)
  Compute gcdn 0 0.                         (* 0 *)
  Compute gcdn 1 0.                         (* 1 *)
  Compute gcdn 0 1.                         (* 1 *)
  Compute gcdn 1 1.                         (* 1 *)
  
  Goal gcd (fib 1) (fib 0) = fib (gcd 1 0).
  Proof.
    rewrite gcd_equation //=.
      by rewrite gcd_equation.
  Qed.
  
(**
functional induction を使って証明します。
*)
  Theorem gcd_fib__fib_gcd (m n : nat) : (gcd (fib m) (fib n) = fib (gcd m n)).
  Proof.
    rewrite gcdC.
    functional induction (gcd m n).
    - rewrite gcdC.
      rewrite gcd_equation.
      done.
    (* 
  IHn0 : gcd (fib m) (fib (n %% m)) = fib (gcd (n %% m) m)
  ============================
  gcd (fib n) (fib m) = fib (gcd (n %% m) m)
     *)
    - rewrite fin_gcd_modr.
      done.
  Qed.
  
End Fib3.

(**
# GCDの帰納法の証明

おまけ。まだうまくいかない。
*)
Section Fib31.

  Lemma gcdn_ind : forall P : nat -> nat -> nat -> Prop,
    (forall m n : nat, m = 0 -> P 0 n n) ->
    (forall m n : nat,
          match m with
          | 0 => False
          | _.+1 => True
          end -> P (n %% m) m (gcdn (n %% m) m) -> P m n (gcdn (n %% m) m)) ->
    forall m n : nat, P m n (gcdn m n).
  Proof.
    move=> P H1 H2 m n.
    rewrite gcdnE /=.
    elim: n.
    - case: m => //=.
      + by apply: H1.
      + move=> n.
        rewrite mod0n gcd0n.
        admit.
    - case: m.
      + move=> n //= H.
          by apply: H1.
      + move=> n n'.
        case H : n.+1 => //=.
        rewrite -H.
        move=> Hc.
        apply: H2 => //.
  Admitted.

  Fail Functional Scheme gcdn_ind := Induction for gcdn Sort Prop.
  (* Error: A fixpoint needs at least one parameter. *)
  
End Fib31.

(**
# 文献

[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition


[1'] 有澤、安村、萩野、石畑訳、「コンピュータの数学」共立出版


[2] D.E.Knuth, "The Art of Computer Programming: Vol.1: Fundamental Algorithms (3rd ed.) "


[3] "GCD of Fibonacci Numbers"、https://proofwiki.org/wiki/GCD_of_Fibonacci_Numbers


[4] ぱるち、「フィボナッチ数列で互除法っぽいこと」、https://mathlog.info/articles/278


[5] 名古屋大学 2021年度秋・数理解析・計算機数学 IV (同 概論IV) "Mathcomp, 自己反映と数論の証明"、
https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2021_AW/ssrcoq5.pdf


[6] https://github.com/suharahiromichi/coq/blob/master/math/ssr_fib_2.v
*)

(* END *)
