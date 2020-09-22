(**
導入記事 01. Coq/SSReflect/MathComp で如何に証明を進めるか
========================

@suharahiromichi

2020/09/21
 *)

(**
# はじめに

形式的な定理証明が何たるか、を理解しているひとのために、MathComp を
使った定理証明の ``How To`` をまとめてみます。
ここに書かれていることを試してみれば、証明のステップを進められるはずです。

証明を完成するには、証明しようとする問題を深く理解することが大切ですが、
それ以前のこととして、このような試行錯誤を経ることも必要だと思います。
 *)

(**
## 用語の定義

Goals ウインドウの ``============================`` 
の上をコンテキスト、下をゴールと呼びます。


下記の ``P``, ``Q``, ``G`` は、量化命題とします。


コンテキストは、

```
x1 : T1
x2 : T2
x3 : T3
H1 : P1
H2 : P2
H3 : P3
```

のように、変数``x``とその型``T``、前提``H``とその命題``P``からなります。


ゴールは、

``Q1 -> Q2 -> Q3 -> G``

のように、前提Qと、結論G を ``->`` でつないだ命題です。``->`` は右結合なので、

``Q1 -> (Q2 -> (Q3 -> G))``

の意味です。また、前提が無い場合のゴールは、``∀y.G`` または ``∃z.G`` のかたちになります。
 *)

(**
## 御注意

この節は、読み飛ばしても構いません。十分理解できた後に読み返してください。

MathComp の case と elim タクティクなどは、
引数なしでは、ゴールの先頭（最左）の前提か全量化変数
（上記の例では ``Q1`` または ``y``）を対象とします。

```Coq
move=> y.
case: y.
```

は、

```Coq
case.
```

と同じです。しかし、慣れないうちは、コンテキストの前提を明示的に指定したほうが
解りやすいこと、Standard Coq とあわせるために、本資料では、
ゴールの前提をコンテキストに移動
してから、case: と elim: タクティクで指定するようにします。

- ただし、*Standard Coqと違って*、case: や elim: の対象とした
コンテキストの変数 ``x`` が、
コンテキストの他の前提``H``に依存する（前提の命題の中に出現する）場合は
エラーになります。この場合は、前提のほうも一緒に指定します。``case: x H``

- elim では、ゴールの全量化変数（∀y）をすべて前提に移動してしまう
（イントロし過ぎてしまう）と、生成される帰納法の仮定にも全量化変数が無くなり、
帰納法の仮定を適用するときに困る場合があります。
このような場合は、イントロし過ぎないようにするしかありません。
なお、このことは、Sarndard Coq でも MathComp でも同様に発生します。
 *)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.                    (* ssromega タクティク *)
Require Import ssrinv.                      (* inv コマンド *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Basic.
(**
# 1. 基本概念：ゴールとコンテキストの間の移動

- ゴールからコンテキストへの移動（intro または pop）
ゴールの先頭にある前提または全量化変数が対象になる
（注意：C-H対応から、両者に区別がない同じものである）。

- コンテキストからゴールへの移動（generalize または push）。
コンテキストを指定しておこなう。
 *)
  
(**
- ゴールが ``Q1 -> G`` のとき、``Q1`` をコンテキストに移動する（intro または pop）。
また、コンテキスト``H1`` をゴールに移動する（generalize または push）。
*)
  Lemma test11 (Q1 G : Prop) : Q1 -> G.
    move=> H1.                              (* intro *)
    move: H1.                               (* generalize *)
  Abort.
         
(**
- ゴールが ``forall x, g x`` のとき、``x`` をコンテキストに移動する。
また、コンテキスト``x`` をゴールに移動する。
*)
  Lemma test12 g : forall (n : nat), g n.
    move=> n.                               (* intro *)
    move: n.                                (* generalize *)
    
    (* intro は別の名前でもよい。 *)
    move=> x.                               (* intro *)
    (* generalize はコンテクストを正しく指定すること。 *)
    move: x.                                (* generalize *)
  Abort.

(**
- 証明済の Lemma なども generalize できる。
（参考：case で他の補題を指定できる。後述）
 *)
  Lemma test13 (P1 : Prop) : True /\ P1 -> True.
    Check proj1 : forall A B : Prop, A /\ B -> A.
    move: proj1.
  Abort.
  
(**
# 2. ゴールの終了
*)

  Lemma test21 (P1 : Prop) : P1 -> True.
    move=> H1.
(**
- ゴールの結論が ``True`` のとき。
 *)
    done.
  Qed.

  Lemma test23 (G : Prop) : G -> G.
    move=> H.
(**
- コンテキストとゴールに同じ命題がある場合。
*)  
    done.
  Qed.

  Lemma test22 (G : Prop) : False -> G.
    move=> Hc.
(**
- コンテキストに ``False`` があるとき、
このとき、結論``G``は何でもよいでもよい。``False`` であってもよい。
 *)
    done.
  Qed.

  Lemma test24 (P1 G : Prop) : P1 -> ~ P1 -> G.
    move=> H1 H2.
(**
- コンテキストに同じ命題の否定がある場合。
このとき、結論``G``は何でもよいでもよい。``False`` であってもよい。
（参考：前提が矛盾なら、常に成立する）
 *)
    done.
  Qed.

  Lemma test25 (n : nat) : n = n.
(**
- ゴールが等式で、右辺と左辺が同じ場合。
*)
    done.
  Qed.
  
(**
# 3. 命題論理の証明
*)
(**
## 含意の証明
 *)
  Lemma test31 (P Q : Prop) : P -> (P -> Q) -> Q.
    move=> HP.
    move=> HPQ.
(**
- ゴールが ``Q`` で、前提に ``P -> Q`` があるなら、その前提をapplyする。
 *)
    apply: HPQ.
    done.
  Qed.
  
(**
## 論理積の証明
 *)
  Lemma test32 (P1 P2 : Prop) : P1 /\ P2 -> P2 /\ P1.
    move=> H.
(**
- 前提に論理積があるなら、その前提を case で分解する。
*)
    case: H.
    
    move=> H1 H2.
(**
- ゴールが論理積なら、splitタクティクを使う。
*)
    split.
    - done.
    - done.
  Qed.

(**
## 論理和の証明
 *)
  Lemma test33 (P1 P2 : Prop) : P1 \/ P2 -> P2 \/ P1.
    move=> H.
(**
- 前提に論理和があるなら、その前提を case で分解する。
*)
    case: H.
    
    - move=> H1.
(**
- ゴールが論理和なら、left または right タクティクを使う。
（参考：これを使うのは、できるだけ後にするとよい）
*)
      right.
      done.
      
    - move=> H1.
(**
- ゴールが論理和なら、left または right タクティクを使う。
（参考：これを使うのは、できるだけ後にするとよい）
*)
      left.
      done.
  Qed.

(**
## 否定の証明

``~ P`` は ``P -> False`` の略記である。
 *)
  Lemma test34 (P1 P2 : Prop) : (P1 -> P2) -> ~ P2 -> ~ P1.
    move=> H.
    move=> Hc.
(**
- ゴールが否定なら intro する。
*)
    move=> H1.
(**
- 前提が否定なら、ゴールが``False`` なら apply する。
 *)
    apply: Hc.

    apply: H.
    done.
  Qed.

(**
# 4. 述語論理
 *)
(**
## 全称記号（∀、すべて）の証明
 *)
  Lemma test40 : forall n : nat, 0 < n + 1.
  Proof.
(**
- ゴールに全称記号がある場合は、intro する。
 *)
    move=> n.
  Abort.
  
  Lemma test41 : (forall (n : nat), 1 + n = n + 1) -> 1 + 3 = 3 + 1.
    move=> H.
(**
- 前提に全称記号がある場合は、その前提に適当な値を適用する。
*)    
    move: (H 3) => H3.
    done.
  Qed.

(**
## 存在記号（∃、ある）の証明
*)  
  Lemma test42 : exists (n : nat), n + 1 = 3.
(**
- ゴールに存在記号がある場合は、適当な値を与える。
（参考：これを使うのは、できるだけ後にするとよい）
 *)
    exists 2.
    done.
  Qed.

  Lemma test43 : (exists (n : nat), n + 1 > 0) -> True.
    move=> He.
(**
- 前提に存在記号がある場合は、その前提を case で場合分けする。
 *)
    case: He.
    move=> x.
    done.
  Qed.

(**
# 5. 等式の証明
 *)
  Lemma test51 (n : nat) : n = n.
(**
- 右辺と左辺が同じ場合は、ゴールが終了する。
*)
    done.
  Qed.

  Lemma test52 (n : nat) : n = 2 -> 5 = n + 3.
    move=> H.
(**
- 前提の左辺を右辺で書き換える。
*)
    rewrite H.
    
    done.                                   (* 簡単な計算なら実施できる。 *)
  Qed.

  Lemma test53 (n : nat) : 2 = n -> 5 = n + 3.
    move=> H.
(**
- 前提の右辺を左辺で書き換える。前提にマイナスをつける。
*)
    rewrite -H.
    
    done.                                   (* 簡単な計算なら実施できる。 *)
  Qed.

  Lemma test54 (f : nat -> nat) (m n : nat) : m = n -> f m = f n.
  Proof.
    move=> H.
(**
- 左辺と右辺に同じ関数が適用されている場合。2変数以上の関数でも可能である。
*)
    congr (f _).                          (* 関数 f(x) を指定する。 *)
    done.
  Qed.

(**
# 6. 不等式（等しくない）の証明

不等式 (≦ や ＜ など）は、自然数の補題を使って証明しますから、ここでは省略します。

- ``m <> n`` は、``m = n -> False`` の構文糖衣なので、否定の証明の応用になります。
*)  
  Lemma test61 (m n : nat) : m <> n -> n <> m.
    move=> H.
    move=> Hc.
    apply: H.
    rewrite Hc.
    done.
  Qed.

(**
-  ``m <> m`` は、成り立ちませんから ``False`` と同じです。
 *)
  Lemma test62 (m : nat) : m <> m -> False.
    move=> H.
    done.
  Qed.
  
(**
# 7. 場合分け
 *)
(**
## 変数の型による場合分け
*)
  Lemma test72 n : 0 <> n -> n <> 0.
  Proof.
    case: n.
    - move=> H.                             (* n = 0 の場合 *)
      done.                                 (* 前提 H : 0 <> 0 で、矛盾 *)
    - move=> n H.
      move=> Hc.
      apply: H.
      rewrite Hc.
      done.
  Qed.

(**
## 命題による場合分け
*)
  Lemma test73 n : 0 <> n -> n <> 0.
  Proof.
    move=> H.
    case: H.
  Admitted.
    
(**
## コンストラクタによる場合分け
 *)
  
(**
# 8. 数学的帰納法
 *)
(**
## 変数の型による帰納法
*)
  Lemma test82 n : 0 < n -> n - 1 + 1 = n.
  Proof.
    elim: n.
    Admitted.

(**
## 命題による帰納法
*)
  Lemma test81 n : 0 < n -> n - 1 + 1 = n.
  Proof.
    move=> H.
    elim: H.
  Admitted.

(**
# 9. 高度な証明
 *)
(**
- auto
*)
(**
- omega と ring
*)  
(**
- inversion
*)


End HowTo.

(* END *)
