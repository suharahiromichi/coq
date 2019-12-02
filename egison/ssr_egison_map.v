(**
Egisonプログラムの証明 - 序論 -
======
2019/12/01

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/egison/ssr_egison_map.v

 *)

(**
OCaml 4.07.1, Coq 8.9.1, MathComp 1.9.0
 *)

(**
# はじめに

プログラミング言語 Egison ([1.]) は、
強力なパターンマッチング機能を特徴とし、他のプログラミング言語とは大きく異なった
意味論を持つようにみえます。
一方で、Egison についても、それで書かれたプログラムについて正しさを証明したい
という願望があります。

そこで、Egisonで書かれたプログラムを証明することへの（個人的な）第一歩として、
Egison の map関数 ([1.]) の意味を定義して、
それが通常の関数型言語の map と同じである
（同じ入力に対して同じ出力を返す）ことを証明してみます。

証明は Coq/MathComp を使用します。MathCompで定義済み（証明済み）の補題などについては、
[2.] を参照してください。
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 証明の方針

[1.] にある、Egison の map関数のコード（説明の都合から wildcard を変数 に変えています）
を対象にします。

```
(define $map
  (lambda [$f $xs]
    (match-all xs (list something)
      [<join $ax <cons $x $bx>> (f x)])))
```

の結果（出力）を ys とします。
このプログラムの意味を与える命題を考えてみます。
述語 egimap は3つの引数をとり、第1引数が適用する ``A -> B`` 型の関数、
第2引数が入力のリスト、この要素すべてにfを適用した結果が第3引数とします。
すると、このプログラムの意味は、

```
egimap f xs ya
```

となります。また以下のように考えられます。

- 入力リスト xs は、リスト ax と 要素 x と、リスト bx に分解される。
- ax は帰納的に、``egimap f ax ay``
- bx は帰納的に、``egimap f bx by``
- 出力リストは、リスト ya と ``f x`` と、リスト by から組み立てられる。


リストの分解と組立ては、
述語 egijoin は3つの引数をとり、第1引数と第2引数を連結した結果が第3引数であるとすると、
``egijoin ax (x :: bx) xs`` と ``egijoin ay (y :: by) ys`` となります。
ここで、「::」はリストの連結(cons)の意味です。

以上をひとつの論理式にまとめると、次のようになります。

```
∀(x : A), ∀(xa xb xs : seq A), ∀(ya yb ys : seq B),
      egijoin xa (x :: xb) xs ->
      egimap f xa ya ->
      egimap f xb yb ->
      egijoin ya (f x :: yb) ys ->
      egimap f xs ys.
```

この論理式が Egison の map プログラムの意味を正しく示していると言えるなら、
それが、関数言語の map と等価であることを示すために、


```
∀(xa : seq A), ∀(ya : seq B), egimap f xs ys <-> map f xs = ys
```

を証明できればよいことになります。
*)

(**
# 証明の詳細

MathComp を使うので、リストは seq になります（バニラCoqのlistと同じですが、
空リストは ``[::]`` で表します。
また、リストの連結を示す関数は cat で、中置演算子 ++ も使えます。

map する関数は ``A -> B`` 型とし、
map の入力のリストを ``seq A``、出力を ``seq B`` とします。
A と B は任意の型で、Section の中で変数として定義していますが、
Section の外からは 「∀」 が付いたかたちで見えます。
*)

(**
## egijoin の定義
*)

(**
まず、egijoin の意味を定義し、それが Coq のリストを連結する cat 関数と等価であることを
証明します。
*)
  
Section List.
  
  Variable A : Type.
  
(**
述語 egijoin は3つの引数をとり、第1引数と第2引数を連結した結果が第3引数であることを示します。
すなわち、``egijoin a b c`` は、a と b を連結したものが c である、
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
  Lemma joincat : forall (a b c : seq A), egijoin a b c <-> a ++ b = c.
  Proof.
    split.
    - elim=> b'' //= a' b' c' H IH.
        by rewrite IH.
    - elim: a b c => //=.
      + move=> b c ->.
          by apply: egi_join_nil.
      + move=> n' a' IH b' c' <-.
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
最後に、命題 ``egimap f xs ys`` が、関数 map の結果 ``map f xs = ys``
と同値であることを証明します。後者の表記は MathComp では ``[seq f i | i <- xs] = ys``
となります。
*)

  Lemma mapmap (f : A -> B) (xs : seq A) (ys : seq B) :
      egimap f xs ys <-> [seq f i | i <- xs] = ys.
  Proof.
    split.
    (* -> の証明 *)
    - elim=> //=.
      move=> x xa xb s ya yb t Hjx Hema Hcma Hemb Hcmb Hjy.
      move/joincat in Hjx.
      move/joincat in Hjy.
      subst.
      
      (* MathComp の証明済みの補題を使います。 *)
      Check map_cat : forall (T1 T2 : Type) (f : T1 -> T2) (s1 s2 : seq T1),
          [seq f i | i <- s1 ++ s2] = [seq f i | i <- s1] ++ [seq f i | i <- s2].
      Check map_cons : forall (T1 T2 : Type) (f : T1 -> T2) (x : T1) (s : seq T1),
          [seq f i | i <- x :: s] = f x :: [seq f i | i <- s].
      
      rewrite map_cat.
      rewrite map_cons.
        by [].                            (* 左辺と右辺が一致する。 *)
      
    (* <- の証明 *)
    - elim: xs ys => //=.
      (* 入力の引数が空リストの場合： *)
      + move=> t H.
        rewrite -H.
          by apply: egi_map_nil.
      + move=> x s IH t H.
        rewrite -H.
        
(**
ここで、egi_map_cons を適用します。適用される引数を省かずに書くと、
次の Check コマンドのようになります。
しかし、この場合は、引数をすべて省略しても Coq が補ってくれます。
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
        * by apply: IH.                     (* 帰納法の仮定を使用する。 *)
        * by apply: egi_join_nil.
  Qed.
  
End map.

(**
# まとめ

Egisonで書かれたプログラムに証明を与えることの一歩として、
map関数の証明（のようなもの）を与えてみました。

実際のEgisonのコードから述語 egimap を求める部分に飛躍があり、
証明遊びの域を出るものではありません。
もし、Egison を Coq や他の証明器で証明することに関心をもたれる方があれば幸いです。
*)

(**
# 参考文献

[1.] 江木 「Egison プログラミング入門」、Egison Journal Vol.1


[2.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版
*)


(* END *)
