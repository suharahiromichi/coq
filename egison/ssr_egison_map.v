(**
Egisonプログラムの証明 - 序論 -
======
2019/12/06


本記事は「Egison Advent Calendar 2019」


https://qiita.com/advent-calendar/2019/egison


の6日目の記事です。
この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/egison/ssr_egison_map.v

 *)

(**
OCaml 4.07.1, Coq 8.9.1, MathComp 1.9.0
 *)

(**
# はじめに

5日めの記事は、Egison **で** 証明を書く話題でした。
今日は、
Egisonプログラム **の** 証明、すなわち、Egison で書いたプログラム自体の正しさの証明ついて、
考えてみたいと思います。

プログラミング言語 Egison ([1.]) は、
他のプログラミング言語とは大きく異なった意味論を持つため、
書かれたプログラムについて正しさを証明するのは難しいように見えます。
それでもなんらかのかたちで、正しさを証明したいという願望があります。

そこで、Egison で書かれたプログラムを証明することの一歩として、
Egison の map プログラム ([1.]) の意味を定義して、
それが通常の関数型言語の map 関数と同じである
（同じ入力に対して同じ出力を返す）ことを証明してみます。

証明は Coq/MathComp を使用します。
Coq/MathComp 全般については[2.] を参照してください。
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 証明の方針

[1.] にある、Egison の map プログラムのコードを対象にします。
説明の都合から wildcard を変数に変えています。

```

(define $map
  (lambda [$f $xs]
    (match-all xs (list something)
      [<join $ax <cons $x $bx>> (f x)])))
```

結果（出力リスト）を ys とします。また、xs を入力リストと呼ぶ場合があります。

このプログラムの意味を与える述語 egimap を考えてみます。
述語 egimap は3つの引数をとり、第1引数を各要素に適用する関数、
第2引数を入力のリスト、出力リストを第3引数とします。
すると、このプログラムの意味は、

```

egimap f xs ya
```

となります。また以下のように考えられます。

1. 入力リスト xs は、リスト ax と 要素 x と、リスト bx に分解される。
2. ax は再帰的に、``egimap f ax ay`` となる。
3. bx は再帰的に、``egimap f bx by`` となる。
4. 出力リストは、リスト ya と ``f x`` と、リスト by から組み立てられる。


ただし、1.以外については説明に飛躍があり、Egisonのソースコードから
これらを言うには、match-all の動作についてもうすこし説明が必要でしょう。


リストの分解と組立てについては、述語 egjoin を考えます。
述語 egijoin は3つの引数をとり、第1引数と第2引数を結合(join)した結果が第3引数であるとします。

すると上記は、 ``egijoin ax (x :: bx) xs`` と ``egijoin ay (y :: by) ys`` となります。
ここで、 ``::`` は、要素のリストへの追加(cons)の意味です。

以上をひとつの論理式にまとめると、次のようになります。

```

∀(A B : Type), ∀(f : A -> B), ∀(x : A), ∀(xa xb xs : seq A), ∀(ya yb ys : seq B),
      egijoin xa (x :: xb) xs ->
      egimap f xa ya ->
      egimap f xb yb ->
      egijoin ya (f x :: yb) ys ->
      egimap f xs ys.
```

この論理式が Egison の map プログラムの意味を正しく示していると言えるなら、
Egison の map プログラムが関数言語の map と等価であることを示すために、


```

∀(A B : Type), ∀(f : A -> B), ∀(xs : seq A), ∀(ys : seq B),
      egimap f xs ys <-> map f xs = ys
```

を証明できればよいことになります。
実際には、入力リストxsが空である場合も考慮する必要があります。
*)

(**
# 証明の詳細

MathComp を使うので、リストは seq になります。
バニラCoqのlistと同じですが、空リストは ``[::]`` で表します。
また、リストの結合をする関数は cat で、中置演算子 ++ も使えます。

map で各要素の適用する関数は ``A -> B`` 型とし、
map の入力のリストを ``seq A``、出力を ``seq B`` とします。
A と B は任意の型で、Section の中で変数として定義していますが、
Section の外からは、各式に ∀(A : Type) と ∀(B : Type) が付くことになります。
*)

(**
## join の定義
*)

(**
まず、egijoin の意味を定義し、それがリストを結合する Coq の cat 関数と等価であることを
証明します。
*)
  
Section List.
  
  Variable A : Type.
  
(**
述語 egijoin は3つの引数をとり、第1引数と第2引数を結合した結果が第3引数であることを示します。
すなわち、``egijoin a b c`` は、a と b を結合したものが c である、
という命題 (Prop) になります。
*)  
  Inductive egijoin : seq A -> seq A -> seq A -> Prop :=
  | egi_join_nil (b : seq A) : egijoin [::] b b
  | egi_join_cons (h : A) (a b c : seq A) :
      egijoin a b c -> egijoin (h :: a) b (h :: c).
  (* Hint Constructors egijoin. *)
  
(**
次に、命題 ``egijoin a b c`` が、関数 cat の結果 ``a ++ b = c`` と
同値であることを証明します。
*)
  Lemma joincat (a b c : seq A) : egijoin a b c <-> a ++ b = c.
  Proof.
    split.
    (* -> の証明 *)
    - elim=> b'' //= a' b' c' H IH. (* 前提 egijoin ... についてのの帰納法を使う。  *)
        by rewrite IH.
    (* <- の証明 *)
    - elim: a b c => //=.      (* リスト a についての帰納法を使う。 *)
      + move=> b c ->.         (* リストが空の場合： *)
          by apply: egi_join_nil.
      + move=> n' a' IH b' c' <-.       (* リストが空ではない場合： *)
        apply: egi_join_cons.
          by apply: IH.
  Qed.
  
End List.

(**
## map の定義
*)

Section map.

  Variable A : Type.
  Variable B : Type.
  
(**
述語 egimap は3つの引数をとり、第1引数が適用する ``A -> B`` 型の関数、
第2引数が入力のリスト、この要素すべてにfを適用した結果が第3引数であることを示します。
すなわち、``egimap f xs ys`` は、xs の各要素に f を適用したものが と ys である、
という命題になります。
*)

  Inductive egimap (f : A -> B) : seq A -> seq B -> Prop :=
  | egi_map_nil : egimap f [::] [::]
  | egi_map_cons (x : A) (xa xb xs : seq A) (ya yb ys : seq B) :
      egijoin xa (x :: xb) xs -> egimap f xa ya -> egimap f xb yb ->
      egijoin ya (f x :: yb) ys -> egimap f xs ys.
  (* Hint Constructors egimap. *)
  
(**
最後に、命題 ``egimap f xs ys`` が、``[seq f i | i <- xs] = ys``
と同値であることを証明します。

``[seq f i | i <- xs]`` は、MathComp の map 関数の構文糖で、
Coqに組み込まれた関数型言語である Gallina を使って定義されています。
ここでは、これを「通常の関数型言語の map 関数」とみなします。

これは次のように、再帰をつかってふつうに定義されています。
*)

(**
  Fixpoint map (T1 T2 : Type) (f : T1 -> T2) (s : seq T1) : seq T2 :=
  match s with
  | [::] => [::]
  | x :: s' => f x :: map s'
  end.
*)

  Lemma mapmap (f : A -> B) (xs : seq A) (ys : seq B) :
      egimap f xs ys <-> [seq f i | i <- xs] = ys.
  Proof.
    split.
    (* -> の証明 *)
    - elim=> //=.            (* 前提 egimap f xs ys についての帰納法を使う。 *)
      move=> x xa xb s ya yb t Hjx Hema Hcma Hemb Hcmb Hjy.
      move/joincat in Hjx.          (* egijoin を ++ に置き換える。 *)
      move/joincat in Hjy.          (* egijoin を ++ に置き換える。 *)
      subst.                        (* 式を整理する。 *)
      
      (* MathComp の証明済みの補題を使います。 *)
      Check map_cat : forall (T1 T2 : Type) (f : T1 -> T2) (s1 s2 : seq T1),
          [seq f i | i <- s1 ++ s2] = [seq f i | i <- s1] ++ [seq f i | i <- s2].
      Check map_cons : forall (T1 T2 : Type) (f : T1 -> T2) (x : T1) (s : seq T1),
          [seq f i | i <- x :: s] = f x :: [seq f i | i <- s].
      
      rewrite map_cat.
      rewrite map_cons.
        by [].                            (* 左辺と右辺が一致する。 *)
      
    (* <- の証明 *)
    - elim: xs ys => //=.           (* リスト xs についての帰納法を使う。 *)
      + move=> t H.                 (* 入力の引数が空リストの場合： *)
        rewrite -H.
          by apply: egi_map_nil.
          
      + move=> x s IH t H.         (* 入力の引数が空ではない場合： *) 
        rewrite -H.
(**
ここで、egi_map_cons を適用します。適用される引数を省かずに書くと、
次の Check コマンドの引数(@から:の前まで)のようになります。
しかしこの場合は、引数をすべて省略しても Coq が補ってくれます。
とても直感的ですね。
 *)
        Check @egi_map_cons f x [::] s (x :: s)
              [::] [seq f i | i <- s] (f x :: [seq f i | i <- s])
          : egijoin [::] (x :: s) (x :: s) ->
            egimap f [::] [::] ->
            egimap f s [seq f i | i <- s] ->
            egijoin [::] (f x :: [seq f i | i <- s]) (f x :: [seq f i | i <- s]) ->
            egimap f (x :: s) (f x :: [seq f i | i <- s]).
        apply: egi_map_cons.          (* 引数を省略しても適用できる。 *)
        
        * by apply: egi_join_nil.
        * by apply: egi_map_nil.
        * by apply: IH.
        * by apply: egi_join_nil.
  Qed.
  
End map.

(**
# まとめ

Egison で書かれたプログラムに証明を与えることの一歩として、
map 関数の証明もどきを与えてみました。
Egison のコードから述語 egimap を求める部分に飛躍があり、
証明遊びの域を出るものではありません。

そのことを除くと（否、除いてはいけませんが）、
Egison のプログラムでの match の対象が list であったため、
リストの結合を意味する join と cat を使い、さらに、
map と cat の関係について証明済みの補題を使うことで、
簡単に証明できました。
しかし、multiset や set の場合は、それらに対応する述語や関数を用意し、
補題も自分で用意することになり、大変になるとおもいます。
Coq/MathCompには集合を扱うライブラリもありますが、おそらく直接は使用できない
でしょう。

また、今回は Coq/MathComp を使用しましたが、
究極の目標は Egison **で** Egison **の** 証明をすることでしょうか。

それにチャレンジしようとする人の参考になれば、幸いです。
*)

(**
# 参考文献

[1.] 江木聡志 「Egison プログラミング入門」、Egison Journal Vol.1, Vol.2


[2.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版
*)


(* END *)
