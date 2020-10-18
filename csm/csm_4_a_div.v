(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

追加 4.A div.v --- 除算のライブラリ

======

2020_8_10 @suharahiromichi

2020_9_16 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Require Import Recdef.
Require Import Wf_nat.
Require Import Program.Wf.

Require Import ssromega.
(**
https://github.com/suharahiromichi/coq/blob/master/common/ssromega.v
もダウンロードして同じディレクトリに置いて、coqc ssromega.v を実行し、
ssromega.vo ができていることを確認してください。
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/div.v
*)

(**
# 除算
 *)
(**
## 除算の定義

ユーグリッド除法 edivn_rec (末尾再帰）で定義される。
*)
Locate "_ %/ _". (* := divn m d : nat_scope (default interpretation) *)
Print divn.
(*
fun m d : nat => (edivn m d).1
 *)
Print edivn.
(* 
fun m d : nat => if 0 < d then edivn_rec d.-1 m 0 else (0, m)

最初に、除数から1を引いておいて、すなわち、``10÷3`` なら ``d = 2`` としておいて、
 *)
Print edivn_rec.
(* 
fun d : nat =>
fix loop (m q : nat) {struct m} : nat * nat :=
  match m - d with
  | 0 => (q, m)
  | m'.+1 => loop m' q.+1
  end

``m - d = 10 - 2 = 7.+1`` と、非零のチェック（停止判定）を兼ねて、
除数から被除数を引いたものから、さらに1を引いて、7 を得ている。
だから、末尾再帰だけみると、本来の除数(3)を引くのと同じで、

```
(m, q) = (10, 0) = (7, 1) = (4, 2) = (1, 3) => (q, m) = (3, 1)
```

となる。
 *)
Compute edivn 10 3.                         (* (3, 1) *)

(**
補足説明：
整礎帰納法をつかって、もうすこし自然な定義で書くことができます。
*)
Section DIV'.
  Fail Fixpoint edivn' (m d q : nat) {struct m} : nat * nat :=
    if d is 0 then (0, m)                   (* 0で割ると0 *)
    else
      let: m' := m - d in
      if m' is 0 then (q, m) else edivn' m' d q.+1.
  
  Function edivn' (m d q : nat) {wf lt m} : nat * nat :=
    if d is 0 then (0, m)                   (* 0で割ると0 *)
    else
      let: m' := m - d in
      if m' is 0 then (q, m) else edivn' m' d q.+1.
  Proof.
    - move=> m d _ n Hd n' H.
      apply/ltP.
        by ssromega.
    - by apply: lt_wf.
  Qed.
(**
しかし、Compute では計算できません。
*)
  Compute edivn' 10 3 0.

(**
Program コマンドを使います。
*)
  Program Fixpoint edivn'' (m d q : nat) {wf lt m} : nat * nat :=
    if d is 0 then (0, m)
    else
      let: m' := m - d in
      if m' is 0 then (q, m) else edivn'' m' d q.+1.
  Obligation 1.
  Proof.
      by ssromega.
  Qed.
(**
こんどは、計算はできるようです。
*)
  Compute edivn'' 10 3 0.
End DIV'.

(**
## 除法の仕様
*)
Print edivn_spec.
(*
Variant edivn_spec (m d : nat) : nat * nat -> Set :=
    EdivnSpec : forall q r : nat,
                m = q * d + r -> (0 < d) ==> (r < d) -> edivn_spec m d (q, r)

除法の定義が、除法の仕様を満たすという補題：
*)
Check edivnP : forall m d : nat, edivn_spec m d (edivn m d).

(**
同様に除法の結果を等式で表した補題：
``q * d + r`` を d で割ると、q 余り r である。

unfoldするより、これを使ったほうが便利です。
*)
Check edivn_eq : forall d q r : nat, r < d -> edivn (q * d + r) d = (q, r).

(**
# 剰余計算

ユーグリッド除法とは別に定義する。
*)
Print modn.
(*
fun m d : nat => if 0 < d then modn_rec d.-1 m else m
*)
Print modn_rec.
(*
fun d : nat =>
fix loop (m : nat) : nat := match m - d with
                            | 0 => m
                            | m'.+1 => loop m'
                            end
*)
Locate "_ %% _". (* := modn m d : nat_scope (default interpretation) *)

(**
## 剰余計算の補題（0で割る場合）
*)
(**
### ``0 / 0 = 0``
*)
Check divn0 : forall m : nat, m %/ 0 = 0.

(**
### ``m % 0 = m``
 *)
Check modn0 : forall m : nat, m %% 0 = m.

(**
### ``0 %| 0`` および ``~~ (0 %| m)``

0は0で割りきれるが、0以外の数は割りきれない。
 *)
Lemma dvd00 : 0 %| 0.
Proof. done. Qed.

Lemma dvd0n' n : 0 < n -> ~~(0 %| n).
Proof. by rewrite dvd0n lt0n. Qed.
  
(**
### ``m = n %[mod 0]`` は ``m = n`` と同値である。
 *)
Lemma modn0' m n : m = n %[mod 0] <-> m = n.
Proof.
  split.
  - by rewrite 2!modn0.
  - done.
Qed.

(**
## 剰余計算の補題（``0 < d`` を条件にするもの。すなわち0割を避けるもの）
*)
(**
### ``0 < d -> d / d = 1``

``d = 0`` なら ``d / d = 0`` なので、その条件を除いている。
*)
Lemma divnn' d : 0 < d -> d %/ d = 1.
Proof. by rewrite divnn => ->. Qed.

(**
### ``0 < d -> m % d < d``

``d = 0`` なら ``m %% 0 = m`` なので、その条件を除いている。
 *)
Lemma ltn_mod' m d : 0 < d -> m %% d < d.
Proof. by rewrite ltn_mod. Qed.

(**
補足： ``0 < d`` ではなく ``0 != d`` を使いたいときは、次の補題で書き換えてください。
*)
Check lt0n : forall n : nat, (0 < n) = (n != 0).

(**
## 奇偶についての補題
*)
Print odd.

(**
### m %% 2 = 0 <-> ~~ odd m.

奇数かどうかは剰余と独立に定義されているので、同値であることを示す補題：
 *)
Lemma modn2' m : m %% 2 = 0 <-> ~~ odd m.
Proof.
  (* modn2 という補題は奇妙である。左辺がnat、右辺がboolである。 *)
  
  Check modn2 m : m %% 2 = odd m.
  (* 当然、右辺が bool -> nat のコアーションになっている。 *)
  Check modn2 m : m %% 2 = nat_of_bool (odd m).
  
  rewrite modn2.
  (* odd m = 0 <-> ~~ odd m *)
  split=> H.
  
  - (* -> *)
    Fail rewrite H.
(**
H : odd m = 0 は、 nat_of_bool のコアーションであるため、``~~ odd m`` を ~~ 0 にする
rewrite をすることはできない。
 *)
    Check H : nat_of_bool (odd m) = O.

    Check eqb0 : forall b : bool, (nat_of_bool b == 0) = ~~ b.
    Check eqb0 (odd m) : (nat_of_bool (odd m) == 0) = ~~ (odd m).
(**
        nat_of_bool (odd m) = O
を
        nat_of_bool (odd m) == 0

にリフレクションすれば、eqb0 を使って、

        ~~ odd m

に書き換えることができる。
 *)
    Check eqb0 : forall b : bool, (nat_of_bool b == 0) = ~~ b.
    move/eqP in H.
    rewrite eqb0 in H.
    done.
    
  - (* <- *)
(**
逆も同様に証明できる。
*)
    apply/eqP.
      by rewrite eqb0.
Qed.

(**
## 2で割る補題
 *)
Print half.                                 (* ./2 *)

(**
「2で割る」は、divn とは無関係に定義されている。
*)
Check divn2 : forall m : nat, m %/ 2 = m./2.

(**
# 整除可能
 *)
(**
## 整除可能の定義
 *)
Print dvdn.                         (* bool述語 *)
(* fun d m : nat => m %% d == 0 *)

(* 除数のほうが前になる。 ``d \ m`` と書く方が一般的かも。  *)
Locate "d %| m". (* := dvdn m d : nat_scope (default interpretation) *)

(**
%% と ``%|`` の間は、``eqP`` によるリフレクションで変換できる。

``d %| m`` の定義 ``m %% d == 0``  から明らかだが、案外気がつかないかも。
 *)
Goal forall m d, m %% d = 0 <-> d %| m.
Proof.
  move=> m d.
  split=> H.
  - apply/eqP.
    done.
  - apply/eqP.
    done.
Qed.

Goal forall m d, m %% d <> 0 <-> ~~(d %| m).
Proof.
  move=> m d.
  split=> H; by apply/eqP.
Qed.

(**
## 整除可能の補題

奇数（であることの判定）と、剰余とは、独立に定義されている。同値であることを証明する。
*)
Lemma dvdn2' n : 2 %| n <-> ~~ odd n.
Proof. by rewrite dvdn2. Qed.

(**
# GCD・LCM

GCDは、ユーグリッドの互除法で定義される。
*)
Print gcdn_rec.                             (* 略 *)
Print gcdn.

Section GCDLCM.
  Variables m n p : nat.

  Check gcdnn n : gcdn n n = n.
  Check gcdnC n m : gcdn n m = gcdn m n.
  Check gcdnA n m p : gcdn n (gcdn m p) = gcdn (gcdn n m) p.
  Check gcd0n n : gcdn 0 n = n.
  Check gcdn0 n : gcdn n 0 = n.
  Check gcd1n n : gcdn 1 n = 1.
  Check gcdn1 n : gcdn n 1 = 1.
  (* 分配則 *)
  Check muln_gcdr m n p : m * gcdn n p = gcdn (m * n) (m * p).
  Check muln_gcdl m n p : gcdn m n * p = gcdn (m * p) (n * p).
  
  Check lcmnC n m : lcmn n m = lcmn m n.
  Check lcmnA n m p : lcmn n (lcmn m p) = lcmn (lcmn n m) p.
  Check lcm0n n : lcmn 0 n = 0.
  Check lcmn0 n : lcmn n 0 = 0.
  Check lcm1n n : lcmn 1 n = n.
  Check lcmn1 n : lcmn n 1 = n.
  (* 分配則 *)
  Check muln_lcmr m n p : m * lcmn n p = lcmn (m * n) (m * p).
  Check muln_lcml m n p : lcmn m n * p = lcmn (m * p) (n * p).

(**
ユーグリッドの互除法の1回分の等式である。
後述のとおり gcdn の定義は ``Fixpoint ... {struct m}`` で定義するために
判りにくいものになっている。また、gcdnEの証明自体、とても複雑であることに注意。

いずれにせよ、gcdn を unfold せずに、この補題を使うこと。
*)  
  Check gcdnE m n : gcdn m n = if m == 0 then n else gcdn (n %% m) m.

(**
有名な公式：
*)  
  Check muln_lcm_gcd m n : lcmn m n * gcdn m n = m * n.
End GCDLCM.  

(**
名古屋大学の講義で GCD の証明が取り上げられています。
ここで GCD は、MathCompとは別の定義の、清礎帰納法で定義しています。

この演習問題 gcd_divides は、MathCompの補題 dvdn_gcdl と dvdn_gcdr、
gcd_max は、dvdn_gcd に対応します。

[https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2019_SS/ssrcoq5.pdf]

補足説明：この講義資料では、GCDを通常の ``Fixpoint ... {struct m}`` では定義できないとして、
清礎帰納法 ``Function ... {wf lt m}`` で定義しています。
*)
Section NU.
  Fail Fixpoint gcd (m n : nat) {struct m} : nat :=
    if m is 0 then n else gcd (n %% m) m.
  
  Function gcd (m n : nat) {wf lt m} : nat :=
    if m is 0 then n else gcd (n %% m) m.
  Proof.
    - move=> m n m0 _.
      (* 除数が0でないことは、Coqにも判っているので、 *)
      (* %% の除数が0でなければ、%% で値は減っていくことを証明する。 *)
      apply/ltP.
        (* Goal : n %% m0.+1 < m0.+1 *)
        by rewrite ltn_mod.
    - exact: lt_wf.
  Qed.
(**
定義がそのまま取り出せるので、gcdnE 相当の補題を用意する必要はありません。
 *)
  Check gcd_equation
    : forall m n : nat, gcd m n = match m with
                                  | 0 => n
                                  | _.+1 => gcd (n %% m) m
                                  end.
(**
しかし、Compute では計算できません。
*)
  Compute gcd 10 3.

(**
ことろで、MathComp では、前述のとおり ``gcdn``
を ``Fixpoint ... {struct m}`` で定義できています。
なぜ、それが可能なのでしょうか？

Fixpoint の場合省略時解釈
で ``{struct id}`` となり、idはCoqが探してくれるのでした。
この場合 ``{struct m}`` に違いありません。

``{struct id}`` は、再帰呼び出し毎に「idが単調減少すること」を示すと説明されますが、
ちょっと正しくありません。実際は、

```
Fixpoint f id := match id with id'.+1 => f id' | ..... end.
``

という ``fix ・・・ match`` の「構造」のなかで減少すること、
つまり match によるパターンマッチを使って
``id - 1 = id'`` という減算が行われることを意味します。

なお、この match は ``if id is id'.+1 then f id' else ....`` というif式でもよいですが、
bool の ``if b then ... else ...`` では、wfのレベルでエラーになるようです。

具体的にいうと、次の ftest1 はFixpoint で定義できます。
 *)
  Fixpoint ftest1 m {struct m} := if m is m'.+1 then ftest1 m' else 0.

(**
パターンマッチではなく、``.-1`` によって減算する場合
は、``{struct m}`` ではエラーになります。   
*)
  Fail Function ftest2 m {struct m} := if m is 0 then 0 else ftest2 m.-1.
  
(**
整礎帰納法を使う必要があります。
*)  
  Function ftest3 m {wf lt m} := if m is 0 then 0 else ftest3 m.-1.
  Proof.
    move=> m m' H.
    - have l_test n : n != 0 -> n.-1 < n by case: n.
        by apply/ltP/l_test.
    - by apply: lt_wf.
  Qed.

(**
MathComp の ``gcdn`` の定義を見ると、技巧的に ``match``
(``if ... is ... then ... else ...``) が使われていることが判ります。

補足終わり。
*)  
End NU.

(**
# 互いに素 (coprime, relatively prime)
*)
(**
## 互いに素の定義
*)
Print coprime.                              (* boolena述語 *)
(**
fun m n : nat => gcdn m n == 1
 *)

Goal forall m n, gcdn m n = 1 <-> coprime m n.
Proof.
  move=> m n.
  split=> H.
  - apply/eqP.
    done.
  - apply/eqP.
    done.
Qed.

(**
## 互いに素の補題
 *)
Check coprime1n : forall n : nat, coprime 1 n.
Check coprimen1 : forall n : nat, coprime n 1.
Check coprime_sym : forall m n : nat, coprime m n = coprime n m.

(**
# 合同式
 *)
(**
## 合同式の定義
 *)
Locate "_ = _ %[mod _ ]".              (* 3項演算子であることに注意 *)
(* := eq (modn m d) (modn n d) : nat_scope (default interpretation) *)

Locate "_ <> _ %[mod _ ]".             (* 3項演算子であることに注意 *)
(* := not (eq (modn m d) (modn n d)) : nat_scope *)

Locate "_ == _ %[mod _ ]".             (* 3項演算子であることに注意 *)
(* := eq_op (modn m d) (modn n d) : nat_scope (default interpretation) *)

Locate "_ != _ %[mod _ ]".             (* 3項演算子であることに注意 *)
(* := negb (eq_op (modn m d) (modn n d)) : nat_scope (default interpretation) *)


(**
## rewrite による書き換え

(m %% d) = (n %% d) の構文糖衣であるので、
``%[mod _]`` すなわち ``%% _`` の部分が一致していれば、rewriteも可能である。
*)
Goal forall m n p d, m = n %[mod d] -> n = p %[mod d] -> m = p %[mod d].
Proof. move=> m n p d H1 H2. rewrite H1 H2. done. Qed.

(**
### 等式の補題の適用

等式の左辺と右辺を入れ替える。
「=」「<>」「==」「!=」についての補題も適用可能である。
*)
Check @esym : forall (A : Type) (x y : A), x = y -> y = x.
Goal forall m n d, m = n %[mod d] -> n = m %[mod d].
Proof. move=> m n d H. by apply: esym. Qed.

Goal 2 = 4 %[mod 2] -> 4 = 2 %[mod 2]. Proof. apply: esym. Qed.

Check @nesym : forall (A : Type) (x y : A), x <> y -> y <> x.
Goal forall m n d, m <> n %[mod d] -> n <> m %[mod d].
Proof. move=> m n d H. by apply: nesym. Qed.

Check eq_sym : forall (T : eqType) (x y : T), (x == y) = (y == x).
Goal forall m n d, m == n %[mod d] -> n == m %[mod d].
Proof. move=> m n d H. by rewrite eq_sym. Qed.

Goal forall m n d, m != n %[mod d] -> n != m %[mod d].
Proof. move=> m n d H. by rewrite eq_sym. Qed.

(**
eqP で、Prop (=) と boolean (==) を変換できます。
*)
Goal forall m n d, m = n %[mod d] <-> m == n %[mod d].
Proof.
  move=> m n d.
  split=> H; by apply/eqP.
Qed.

Goal forall m n d, m <> n %[mod d] <-> m != n %[mod d].
Proof.
  move=> m n d.
  split=> H; by apply/eqP.
Qed.

(**
### congr で、%[mod d] を外す

ここで「外す」とは、``->``の右から左に変換することです。逆は成り立ちません。
*)
Goal forall m n d, m = n -> m = n %[mod d].
Proof.
  move=> m n d H.
  (* Goal : m = n %[mod d] *)
  congr (_ %% d).
  (* Goal : m = n *)
  done.
Qed.

Section Modulo.
(**
## Concrete Mathematics [1] （コンピュータの数学 [2]） 4.6 合同関係 の公式

変数名 m n p q d d1 d2 の使い方は、MathComp の div.v [3] にあわせています。
*)
  
(**
### 合同式の加算

「合同な要素を足しても、合同関係は崩れない。」

$$ m = n \pmod{d} \Longrightarrow 
   p = q \pmod{d} \Longrightarrow 
   m + p = n + q \pmod{d} $$
 *)  
  Lemma m_addn m n p q d  :
    m = n %[mod d] -> p = q %[mod d] -> m + p = n + q %[mod d].
  Proof.
    move=> Hmp Hnd.
    Check modnDm : forall m n d : nat, m %% d + n %% d = m + n %[mod d].
    rewrite -[LHS]modnDm -[RHS]modnDm.
    (* m %% d + p %% d = n %% d + q %% d %[mod d] *)
    
    congr (_ %% _).            (* %[mod d] を外す。 *)
    (* m %% d + p %% d = n %% d + q %% d *)
    
    congr (_ + _).
    (* m %%d = n %% d *)
    - done.
    (* p %%d = q %% d *)
    - done.
  Qed.
  
(**
### 合同式の乗算

「掛け算もうまくいく。」

$$ m = n \pmod{d} \Longrightarrow 
   p = q \pmod{d} \Longrightarrow 
   m p = n q \pmod{d} $$
 *)  
  Lemma m_muln m n p q d  :
    m = n %[mod d] -> p = q %[mod d] -> m * p = n * q %[mod d].
  Proof.
    move=> Hmp Hnd.
    Check modnMm : forall m n d : nat, m %% d * (n %% d) = m * n %[mod d].
    rewrite -[LHS]modnMm -[RHS]modnMm.
    
    congr (_ %% _). (* %[mod d] を外す。 *)
      (* Goal : m %% d * (p %% d) = n %% d * (q %% d) *)
      by congr (_ * _).
  Qed.
  
(**
``p = q`` である特別な場合について証明しておきます。後で使います。
 *)
  Lemma m_muln' m n p d  :
    m = n %[mod d] -> m * p = n * p %[mod d].
  Proof.
    move=> H.
      by apply: m_muln.
  Qed.
  
(**
### 合同式のべき乗

「掛け算の性質を繰り返し適用すると、べき乗することもできる。」

$$ p = q \pmod{d} \Longrightarrow p^{m} = q^{m} \pmod{d} $$
 *)  
  Lemma m_exprn p q m d :
    p = q %[mod d] -> p^m = q^m %[mod d].
  Proof.
    move=> Hpq.
    Check modnXm : forall m d p : nat, (p %% d) ^ m = p ^ m %[mod d].
    rewrite -[LHS]modnXm -[RHS]modnXm.
    
    congr (_ %% _).
      (* Goal : (p %% d) ^ m = (q %% d) ^ m *)
      by congr (_ ^ _).
  Qed.
  
(**
### 合同式の除算（式(4.37)）

「(p と d が)互いに素の場合には、(dを法とする)合同関係のもとでも(pによる)割り算ができる。」

$$ m p = n p \pmod{d} \Longleftrightarrow m = n \pmod{d}, 但し p \perp d $$

説明：まず、[1]の式(4.37) の→を証明します。
拡張したGCDを使用するので [3] の chinese_modl 補題の証明、および、
その解説の [4] も参考にしてください。
 *)  
  Lemma m_divn_d_1 m n p d :
    coprime p d -> m * p = n * p %[mod d] -> m = n %[mod d].
  Proof.
    rewrite /coprime => /eqP.               (* 前提を gcdn p d = 1 *)
    
    (* p = 0 と 0 < p に場合分けする。 *)
    case: (posnP p).
    
    (* p = 0 の場合 *)
    - move=> ->.                            (* p = 0 で書き換える。 *)
      rewrite gcd0n.                        (* 前提から d = 1 でもある。 *)
      move=> ->.                            (* d = 1 で書き換える。 *)
        by rewrite !modn1.
        
    (* 0 < p の場合 *)
    - move=> p_gt0 Hco.     (* 0 < p 条件と、coprime条件を intro する。 *)
      
      Check @egcdnP p d p_gt0 : egcdn_spec p d (egcdn p d).
      case: (@egcdnP p d p_gt0). (* 拡張ユーグリッドの互除法の定義を前提に積む。 *)
      (* egcdn_spec は inductive に定義されているので、条件がひとつでも case が要る。 *)
      (* km * p = kn * d + gcdn p d と kn * gcdn p d < p *)
      
      move=> p' d' Hdef _ H.
      rewrite Hco in Hdef.
      (* ``Hdef : p' * p = d' * d + 1`` は不定方程式を展開した状態である。 *)
    
      (* H の 両辺に p' をかける。 p' が p の逆数のような働きをする。 *)
      Check @m_muln' (m * p) (n * p) p' d
        : m * p = n * p %[mod d] -> m * p * p' = n * p * p' %[mod d].
      move/(@m_muln' (m * p) (n * p) p' d) in H.
      
      (* 不定方程式 ``Hdef`` を H に代入して整理する。 *)
      rewrite -2!mulnA -[p * p']mulnC in H.
      rewrite Hdef in H.
      rewrite 2!mulnDr 2!muln1 2!mulnA 2!modnMDl in H.
      done.
  Qed.
  
(**
[1]の式(4.37) の←は、掛け算の合同の公式から明らかなので、<->が証明できます。
*)
  Lemma m_divn_d' m n p d :
    coprime p d -> (m * p = n * p %[mod d] <-> m = n %[mod d]).
  Proof.
    move=> Hco.
    split.
    - by apply: m_divn_d_1.                 (* -> *)
    - by apply: m_muln'.                    (* <- *)
  Qed.

(**
MathCompらしく、bool値の同値で証明しておきます。
 *)
  Lemma m_divn_d m n p d :
    coprime p d -> (m * p == n * p %[mod d]) = (m == n %[mod d]).
  Proof.
    move=> Hco.
    apply/idP/idP; move/eqP => H; apply/eqP.
    - by apply: (@m_divn_d_1 _ _ p _).      (* -> *)
    - by apply: m_muln'.                    (* <- *)
  Qed.

(**
### 合同式の除算（式(4.38)、法を割る）

「合同関係で割り算をするもうひとつの方法は、法とする自身も他の数と同じように割ることである。
これは、modの分配則だけに依存している。」

$$ m d1 = n d1 \pmod{d2 d1} \Longleftrightarrow m = n \pmod{d2}, 但し 0 \lt d1 $$
 *)  
  Lemma m_divn_dp m n d1 d2 :
    0 < d1 -> (m * d1 == n * d1 %[mod d2 * d1]) = (m == n %[mod d2]).
  Proof.
    move=> Hd1.
    rewrite -[RHS](eqn_pmul2r Hd1). (* 右辺の両辺にd1を掛ける。d1≠0なので可能である。 *)
    
    (* d1による）剰余の分配則を適用する。これも d1≠0なので可能である。 *)
    Check @muln_modl d1 : forall m d : nat, 0 < d1 -> m %% d * d1 = (m * d1) %% (d * d1).
      by rewrite 2!(muln_modl Hd1).
  Qed.
  
(**
### 最大公約数を法とする合同式（式(4.41)）

$$ m = n \pmod{lcm(d1,d2)} \Longleftrightarrow \\
   m = n \pmod{d1} \ かつ\ m = n \pmod{d2} $$

説明：まず、最大公約数とdivisibleの関係を使いやすい補題にしておきます。
 *)
  Lemma lcmn_dvdn d1 d2 m : lcmn d1 d2 %| m -> d1 %| m.
  Proof.
    Check dvdn_lcm d1 d2 m : (lcmn d1 d2 %| m) = (d1 %| m) && (d2 %| m).
    rewrite dvdn_lcm => /andP.
      by case.
  Qed.
  
  Lemma dvdn_lcmn d1 d2 m : d1 %| m -> d2 %| m -> lcmn d1 d2 %| m.
  Proof.
    rewrite dvdn_lcm => H1 H2.
    apply/andP.
      by split.
  Qed.
  
(**
式(4.41)の→の共通部分です。
*)
  Lemma m_divn_lcmn_1_1_1 m n d1 d2 :
    n <= m -> m = n %[mod lcmn d1 d2] -> m = n %[mod d1].
  Proof.
    Check eqn_mod_dvd
      : forall d m n : nat, n <= m -> (m == n %[mod d]) = (d %| m - n).
    
    move=> Hnm /eqP H.
    rewrite eqn_mod_dvd in H; last done.
    move/lcmn_dvdn in H.
    
    apply/eqP.
    rewrite eqn_mod_dvd; last done.
    done.
  Qed.
  
(**
式(4.41)の→の補題で、証明の中核となる部分です。
場合分けしてそれぞれに共通部分を適用します。
*)
  Lemma m_divn_lcm_1_1 m n d1 d2 :
    m = n %[mod lcmn d1 d2] -> m = n %[mod d1].
  Proof.
    move=> H.
    Check (leq_total m n) : (m <= n) || (n <= m).
    case/orP: (leq_total n m) => Hnm.
    
    (* n <= m である場合 *)
    - by apply: m_divn_lcmn_1_1_1 H.
      
    (* m <= n である場合 *)
    - apply/esym.               (* 合同式の左辺と右辺を入れ替える。 *)
      move/esym in H.           (* 合同式の左辺と右辺を入れ替える。 *)
        by apply: m_divn_lcmn_1_1_1 H.
  Qed.
  
(**
式(4.41)の→の証明です。
*)  
  Lemma m_divn_lcm_1 m n d1 d2 :
    m = n %[mod lcmn d1 d2] -> m = n %[mod d1] /\ m = n %[mod d2].
  Proof.
    split.
    Check @m_divn_lcm_1_1 m n d1 d2 : m = n %[mod lcmn d1 d2] -> m = n %[mod d1].
    - by apply: m_divn_lcm_1_1 H.
    - rewrite lcmnC in H.
        by apply: m_divn_lcm_1_1 H.
  Qed.

(**
式(4.41)の←の補題です。
*)
  Lemma m_divn_lcm_2_1 m n d1 d2 :
    n <= m -> m = n %[mod d1] -> m = n %[mod d2] -> m = n %[mod lcmn d1 d2].
  Proof.
    move=> Hnm /eqP H1 /eqP H2.
    rewrite eqn_mod_dvd in H1; last done.
    rewrite eqn_mod_dvd in H2; last done.
    
    apply/eqP.
    rewrite eqn_mod_dvd; last done.
    
    Check dvdn_lcmn : forall d1 d2 m : nat, d1 %| m -> d2 %| m -> lcmn d1 d2 %| m.
      by apply: dvdn_lcmn.
  Qed.
  
(**
式(4.41)の←の証明です。
*)  
  Lemma m_divn_lcm_2 m n d1 d2 :
    m = n %[mod d1] -> m = n %[mod d2] -> m = n %[mod lcmn d1 d2].
  Proof.
    move=> H1 H2.
    case/orP: (leq_total n m) => Hnm.
    (* n <= m の場合 *)
    - by apply: m_divn_lcm_2_1.       (* 先の補題がそのまま使える。 *)
      
    (* m < n の場合 *)      
    - apply/esym. (* ゴールと条件の合同式の左辺と右辺を入れ替える。 *)
      move/esym in H1.
      move/esym in H2.
        by apply: m_divn_lcm_2_1.     (* 先の補題が使えるようになった。 *)
  Qed.
  
(**
式(4.41)の証明です。MathComp風に、bool値の同値の式としました。
*)  
  Lemma m_divn_lcm m n d1 d2 :
    (m == n %[mod lcmn d1 d2]) = (m == n %[mod d1]) && (m == n %[mod d2]).
  Proof.
    apply/idP/idP => [/eqP H | /andP [/eqP H1 /eqP H2]].
    - move/m_divn_lcm_1 in H.
      case: H => [H1 H2].
        by apply/andP; split; apply/eqP.
    - apply/eqP.
        by apply: m_divn_lcm_2.
  Qed.
  
(**
### 中国人の剰余定理の特別な場合（式(4.42)）

$$ m = n \pmod{d1 d2} \Longleftrightarrow \\
   m = n \pmod{d1}\ かつ\ m = n \pmod{d2}, 但し d1 \perp d2 $$

説明： 互いに素なら、LCMは積であることを証明します。
補題 ``muln_lcm_gcd m n : lcmn m n * gcdn m n = m * n`` を使います。
*)  
  Lemma coprime_lcm d1 d2 : coprime d1 d2 -> lcmn d1 d2 = d1 * d2.
  Proof.
    rewrite /coprime.
    move=> /eqP Hco.
    Check muln_lcm_gcd : forall m n : nat, lcmn m n * gcdn m n = m * n.
      by rewrite -muln_lcm_gcd Hco muln1.
  Qed.

(**
その補題を使用すれば、式(4.41)からただちに求められます。
これは、中国人の剰余定理の特別な場合です。``div.v`` の
補題 ``chinese_remainder`` と同内容です。
*)  
  Lemma m_chinese_remainder m n d1 d2 :
    coprime d1 d2 ->
    (m == n %[mod d1 * d2]) = (m == n %[mod d1]) && (m == n %[mod d2]).        
  Proof.
    move=> Hco.
    rewrite -coprime_lcm; last done.
      by apply: m_divn_lcm.
  Qed.
  
(**
@morita_hm さんによる別の証明（なお、一部修正しました）。

eqn_mod_dvd を使って、合同式を整除可能に書き換えたあと、
Gauss_dvd を使って、整除可能の * と && の同値関係で証明をします。
Gauss_dvd の証明には mulm_lcm_gcd を使っています(div.vにて)。

なお、eqn_mod_dvd を使うために ``(m <= n)`` と ``(n <= m)`` の場合分けしています。
これは、前提によらす使用することができますので、覚えておくと便利です。

補足説明：bool式の真偽での場合分け ``case H : (m <= n)`` では、
``(m <= n)`` と ``(n < m)`` となり、
後者の条件を ``(n <= m)`` に書き換えるには ltnW が必要になります。不使用補題参照。
*)
  Check eqn_mod_dvd
    : forall d m n : nat, n <= m -> (m == n %[mod d]) = (d %| m - n).
  
  Check Gauss_dvd
    : forall d1 d2 p : nat, coprime d1 d2 -> (d1 * d2 %| p) = (d1 %| p) && (d2 %| p).
  
  Lemma chinese_remainder_lite : forall d1 d2 m n : nat,
      coprime d1 d2 ->
      (m == n %[mod d1 * d2]) = (m == n %[mod d1]) && (m == n %[mod d2]).
  Proof.
    move=> d1 d2 m n co_mn.
    case/orP: (leq_total m n) => geq_mn. (* || を && にリフレクトして場合分けする。 *)
    
    - (* (m <= n) の場合 *)
      rewrite ![m == n %[mod _]]eq_sym.     (* 右辺と左辺を入れ替える。 *)
      rewrite !eqn_mod_dvd //.
        by rewrite Gauss_dvd.
        
    - (* (n <= m) の場合*)
      rewrite !eqn_mod_dvd //.
        by rewrite Gauss_dvd.
  Qed.
  
(**
中国人の剰余定理のより一般的な証明は、``div.v`` の ``chinese_mod`` を参照してください。
 *)
End Modulo.

(**
[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition, A.W.


[2] 有澤、安村、萩野、石畑訳、「コンピュータの数学」共立出版


[3] math-comp/mathcomp/ssreflect/div.v

https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/div.v


[4] 中国人の剰余定理

https://qiita.com/suharahiromichi/items/1a135d9648a0f55f020a

 *)

(**
# 不使用補題
*)

(**
自然数の減算 ``m - n`` を含む証明の場合、``n <= m`` と ``m < n`` で場合分けします。
しかし ``m < n -> m <= n`` なので、後者の条件を ``m <= n`` に変形できれば、
同じ補題が使えるわけです。その変形をする補題を証明しておきます。
*)
  Lemma le_m_n m n : (n <= m) = false -> m <= n. (* 不使用 *)
  Proof.
    move/negbT => Hmn.
    rewrite -ltnNge in Hmn.
      by rewrite ltnW //.
      
    Restart.
    move=> Hmn.
      by ssromega.
  Qed.
(**
``case H : (n <= m)`` なら必要となるが、``case/orP: (leq_total n m)`` でなら
``n <= m`` と ``m <= n`` に分けられるので使わなくてよい。
*)
  

(* END *)
