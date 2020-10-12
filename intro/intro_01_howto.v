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

(**
# 目次

1. 基本概念
1.2 ゴールとコンテキストの間の移動
1.2 （サブ）ゴールの終了
2. いろいろな証明
2.1 命題論理の証明
- 含意の証明
- 論理積の証明
- 論理和の証明
- 否定の証明
2.2 述語論理の証明
- 全称記号（∀、すべて）の証明
- 存在記号（∃、ある）の証明
2.3 等式の証明
2.4 不等式（<>）の証明
2.5 不等式（≦ や ＜）の証明
3. 場合分け
- 変数の型による場合分け
- 命題による場合分け
- コンストラクタによる場合分け
4. 数学的帰納法
- 変数の型による帰納法
- 命題による帰納法
4. 高度なタクティク
4.1 auto
4.2 omega (ssromega)
4.3 inversion (inv)
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.                    (* ssromega タクティク *)
Require Import ssrinv.                      (* inv タクティク *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Basic.
(**
# 1. 基本概念

## 1.2 ゴールとコンテキストの間の移動

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
## 1.2 （サブ）ゴールの終了
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
# 2. いろいろな証明

## 2.1 命題論理の証明
*)
(**
### 含意の証明
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
### 論理積の証明
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
### 論理和の証明
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
### 同値の証明
 *)
  Lemma test35 (m n : nat) : m = n <-> n = m.
  Proof.
(**
- ゴールに <-> があるなら、ゴールを split で -> と <- に分解する。
*)
    split.
    - move=> H.                             (* m = n -> n = m *)
      rewrite H.
      done.
    - move=> H.                             (* n = m -> m = n *)
      rewrite H.
      done.
  Qed.
  
(**
### 否定の証明

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
## 2.2 述語論理の証明
 *)
(**
### 全称記号（∀、すべて）の証明
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
### 存在記号（∃、ある）の証明
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
## 2.3 等式の証明
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
## 2.4 不等式（<>）の証明

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
## 2.5 不等式（≦ や ＜）の証明

自然数についての述語論理であり、自然数の補題を使って証明しますから、ここでは省略します。
*)
  
(**
# 3. 場合分け
 *)
(**
## 変数の型、あるいは、コンストラクタによる場合分け
*)
(**
 *)
  Inductive windrose :=
  | N
  | E
  | S
  | W.
  
  Definition w2n (d : option windrose) : nat :=
    match d with
    | Some N => 0
    | Some E => 1
    | Some S => 2
    | Some W => 3
    | None => 4
    end.
  
  Definition n2w (n : nat) : option windrose :=
    match n with
    | 0 => Some N
    | 1 => Some E
    | 2 => Some S
    | 3 => Some W
    | _ => None
    end.  
  
  Lemma test74 (d : option windrose) : n2w (w2n d) = d.
  Proof.
    (* option _ 型で、場合分けする。 *)
    case: d.
    - move=> a.                             (* Some のとき。 *)
      (* windrose 型で、場合分けする。 *)
      case: a.
      + done.                               (* N のとき、 *)
      + done.                               (* E のとき、 *)
      + done.                               (* S のとき、 *)
      + done.                               (* E のとき、 *)
    - done.                                 (* None のとき。 *)
  Qed.
  
(**
自然数は、``O`` と ``S n`` の場合分けで定義されているので、
変数 n が自然数のとき、``case: n`` で、``O`` と ``S n`` に場合分けできる。

Inductive nat : Set :=
| O
| S (n : nat).
 *)
  Lemma test72 n : n + 1 = 1 + n.
  Proof.
    case: n.
    - done.                                 (* n = 0 の場合 *)
    - move=> n.                             (* n = n.+1 の場合 *)
      (* n.+1 + 1 = 1 + n.+1 *)
      rewrite addn1 add1n.
      (* n.+2 = n.+2 *)
      done.
  Qed.
  
(**
## if式の場合分け
*)

(**
- if式の条件分けは、ifP と覚えてもよい。
*)
  Lemma test76 (n  : nat) : if n == 42 then true else true.
  Proof.
    case: ifP.
    - done.                             (* n == 42 の場合 *)
    - done.                             (* (n == 42) = false の場合 *)
  Qed.

(**
- ifの条件式が、「==」または「!=」である場合に限り、eqP で場合分けできる。

このとき、前提がProp述語になる。
eqP は bool述語（==）とProp述語（=）のリフレクション述語である。
*)  
  Lemma test77 (n  : nat) : if n == 42 then true else true.
  Proof.
    case: eqP.
    - done.                             (* n = 42 の場合 *)
    - done.                             (* n <> 42 の場合 *)
  Qed.
  
(**
- 条件式のtrueとfalseで場合分けする。Hに条件を覚えておいてくれる。

ifの条件式boolであるので、bool型の値trueとfalseで場合分けしている。
だから、これもコンストラクタによる場合分けである。
 *)
  Lemma test73 (n  : nat) : if n == 42 then true else true.
  Proof.
    case H : (n == 42).                     (* 括弧を忘れない。 *)
    - done.                             (* (n == 42) = true の場合 *)
    - done.                             (* (n == 42) = false の場合 *)
  Qed.

(**
# 8. 数学的帰納法
 *)
  Inductive ev : nat -> Prop :=
  | Ev0 : ev 0
  | Ev2 (n : nat) : ev n -> ev n.+2.

  Fixpoint evenb (n : nat) : bool :=
    match n with
    | 0 => true
    | 1 => false
    | n.+2 => evenb n
    end.
  
(**
## 変数の型による帰納法
*)
  Lemma test81  (n : nat) : evenb n = ~~ evenb n.+1.
  Proof.
    elim: n.
    - rewrite /=.
      done.
    - move=> n IHn.
      rewrite [RHS]/=.
      rewrite IHn.
      rewrite negbK.
      done.
  Qed.

(**
## 命題による帰納法
*)
  Lemma ev_even (n : nat) : ev n -> evenb n.  
  Proof.
    move=> H.
    elim: H.
    - done.                                 (* Ev0 : ev 0 *)
    - move=> n' H IHn.                      (* EvS : en' n -> evenb n' *)
      rewrite /=.                           (* evenb n'.+2 *)
      done.
  Qed.

(**
# 9. 高度な証明
 *)
(**
## 9.1 done

*)

(**
## 9.1 simpl (rewrite /=)

csm_3_6_3_simpl.v
*)  

(**
## 9.2 auto

導出原理を使用した自動証明をおこなう。P, Q, R は述語論理の命題でもよい。
*)
  Lemma Sample_of_auto (P Q R : Prop) : P -> (P -> Q) -> (Q -> R) -> R.
  Proof.
    move=> HA HAB HBC.
    auto.
  Qed.
  
  Lemma Sample_of_auto' (P Q : Prop) : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof.
    move=> H.
    auto.
  Qed.
  
(**
## 9.3 omega

ブレスバーガー算術による数式の証明をおこなう。

   ・割り算無し。
   ・変数と変数の掛け算が入っていない。
   ・変数と定数（2, 3などの具体的な整数）の掛け算はOK。
   
   みたいな感じの等式 or 不等式を証明します。
*)
  Lemma Sample_of_omega (x : nat) : x > 1 -> 3 * x > x + 2.
  Proof.
    move=> H.
    ssromega.
  Qed.
  
(**
## 9.4 ring

環に関する数式の自動証明をおこなう。
*)
  Require Import ZArith Ring.
  Open Scope Z_scope.
  Lemma Sample_of_ring : forall a b:Z, a + b = 7 -> a * b = 12 -> a^2 + b^2 = 25.
  Proof.
    move=> a b H1 H2.
    have -> : a^2 + b^2 = (a + b)^2 - 2 * a * b by ring.
    have -> : 2 * a * b = 2 * 12 by ring [H2].
    rewrite H1.
    done.
  Qed.
  Close Scope Z_scope.
  
(**
## 9.5 inversion

コンストラクタを分解する。
*)
  Lemma test95 : ~ (ev 3).
  Proof.
    move=> H3.                              (* H3 : ev 3 *)
    inv: H3.
    move=> H1.                              (* H1 : ev 1 *)
    inv: H1.
  Qed.

  Lemma ev_even' (n : nat) : ev n -> evenb n.
  Proof.
    move=> H.
    inv: H.
    - done.
    - move=> H0.
      rewrite /=.
  Admitted.
    

End Basic.

(* END *)
