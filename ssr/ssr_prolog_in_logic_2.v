(**
論理としてのProlog (その2)
========================

@suharahiromichi

2022/12/22
 *)

(**
もう少し、Prologのプログラムで遊んでみようと思います。

[1] では、特定の値について、つまり``rev([1,2,3], [3,2,1])``だけの証明をしましたが、
今回は、任意の値について証明してみましょう。

Coq/MathCompには、証明済みのappend ``++``や reverse``rev``
関数が用意されているので、
それと同じ結果が得られることを証明するのが簡単だと思います。
Coq/MathCompで用意されている補題を使うことができるからです。

この記事のソースコードは以下にありますが、実行にはCoq/MathCompは必要です。


https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_prolog_in_logic_2.v

*)

From mathcomp Require Import all_ssreflect.

(**
# append の証明

簡単な例として、リストを連結するappendの証明をしてみます。Prologでは、append述語
``append``は、次のように定義されます。ここではλPrologのstdlibから採っています。

```prolog
pred append i:list A, i:list A, o:list A.
append [X|XS] L [X|L1] :- append XS L L1 .
append [] L L .
```
 *)

Variable T : Type.

Lemma rev_nil : @rev T [::] = [::].
Proof.
  done.
Qed.
  
Module LApp.

(**
今回は、Coqで扱い易いように、PrologのプログラムをHypothesisとして定義します。
*)
  Variable append : list T -> list T -> list T -> Prop.
  Hypothesis ap1 : forall (X : T) (XS L L1 : list T),
      append XS L L1 -> append (X :: XS) L (X :: L1).
  Hypothesis ap2 : forall (L : list T), append [::] L L.

(**
Prologのプログラム``append``の第1引数(``XS``)と第2引数(``L``)に対して、
これらを連結したものが、第3引数の``XS ++ L``になることを証明します。

Prologのプログラムと同様に、``append``の第1引数のリストについての帰納法で
証明します。
*)
  Theorem app3_app XS L : append XS L (XS ++ L).
  Proof.
    elim: XS => /= [| X XS IH].
    - by apply: ap2.
    - by apply: ap1.
  Qed.

End LApp.

(**
# reverse の証明

[1]でも取り上げたreverseについて証明します。
Prologの述語とCoq/MathCompの関数名が重複してしまうので、
Prologの述語のほうを``rev2``と改名しています。
それ以外は、Hypothesisとして定義したことを除いて、変わりはありません。

```Prolog
pred rev2 i:list A, o:list A.
rev2 L RL  :- rev3 L []  RL.
rev3 [X|XS] ACC R :- rev3 XS [X|ACC] R.
rev3 [] L L.
```

*)
Module LRev.

  Variable rev2 : list T -> list T -> Prop.
  Variable rev3 : list T -> list T -> list T -> Prop.

  Hypothesis rv0 : forall L RL, rev3 L [::] RL -> rev2 L RL.
  Hypothesis rv1 : forall X XS ACC RL,
      rev3 XS (X :: ACC) RL -> rev3 (X :: XS) ACC RL.
  Hypothesis rv2 : forall RL, rev3 [::] RL RL.
      
(**
## ループ不変式

補助述語rev3が定義されているため、証明はちょと複雑になります。
rev3の実行をトレースしてみます。

```Prolog
enter: rev3([1,2,3],   [],      RL)
enter: rev3([2,3],     [1],     RL)
enter: rev3([3],       [2,1],   RL)
enter: rev3([],        [3,2,1], RL)
exit:  rev3([],        [3,2,1], [3,2,1])
exit:  rev3([3],       [2,1],   [3,2,1])
exit:  rev3([2, 3],    [1],     [3,2,1])
exit:  rev3([1, 2, 3], [],      [3,2,1])
```

``rev3``の、第1引数をreverseして第2引数にappendしたものが第3引数になっているようです。
このことを証明してみましょう。

これは常に成り立つので「ループ不変式」といいます。
途中で、MathCompの``rev``と``++``関数について、
``rev (a :: A) ++ B = rev A ++ (a :: B)`` 
であることを証明する必要が生じましたが、MathCompの補題で証明できました。
*)
  Lemma rev3_invariant A B : rev3 A B (rev A ++ B).
  Proof.
    elim: A B rv1 rv2 => //= a A IHA B Hcons Hnil.
    apply: (Hcons).
    have -> : rev (a :: A) ++ B = rev A ++ (a :: B)
      by rewrite -[a :: A]cat1s rev_cat -catA.
    by apply: IHA.
  Qed.
  
(**
## rev3 についての補題

rev3 について、第1引数をreverseしたものは第3引数であることは、
さきの補題の特殊な場合として、簡単に証明できます。
*)
  Lemma rev3_rev L : rev3 L [::] (rev L).
  Proof.
    rewrite -[rev L]cats0.
    by apply: rev3_invariant.
  Qed.

(**
## 証明したかった定理

証明したいのは、2引数の``rev2``についてですが、
これも上の命題からから簡単に証明できます。
*)
  Theorem rev2_rev L : rev2 L (rev L).
  Proof.
    apply: rv0.
    by apply: rev3_rev.
  Qed.
  
End LRev.

(**
# もうすこし複雑なプログラム

もう少し複雑なプログラムを証明してみましょう。
といっても、append述語を使ってreverseを定義した述語です。
証明の過程で、最初に証明した``app3_app``を使用しています。

```prolog
reverse [X | XS] L2 :-
    reverse XS L,
    append L [X] L2.
reverse [] [].
```
 *)
Module Rev2.
  
  Variable rev2 : list T -> list T -> Prop.
  Hypothesis rv1 : forall (X : T) (XS L L2 : list T),
      rev2 XS L -> LApp.append L [:: X] L2 -> rev2 (X :: XS) L2.
  Hypothesis rv2 : rev2 [::] [::].

  Theorem rev2_rev XS : rev2 XS (rev XS).
  Proof.
    elim: XS => /= [| X XS IH].
    - rewrite rev_nil.
      by apply: rv2.
    - apply: rv1.
      + by apply: IH.
      + rewrite -[X :: XS]cat1s rev_cat.
        by apply: LApp.app3_app.
  Qed.

End Rev2.

(**
# まとめ

証明の説明は省いたため、Coqに親しみのない場合は難しいと思いますが、
論理型言語Prologであっても、プログラムとしての証明は、それほど簡単ではなく、
とくに、実装によって証明が全く変わることなど、手続き型言語や関数型言語と
違いは大きくないと、言えるのではないでしょうか。
*)

(**
# 文献

[1] 論理としてのProlog

https://qiita.com/suharahiromichi/items/c4427a21a7d11f468e39

(* END *)
