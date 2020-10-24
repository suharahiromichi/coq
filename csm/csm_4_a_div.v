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

以下を参照してください：

コンピュータの数学 4.6 合同関係 の公式の証明

https://qiita.com/suharahiromichi/items/01b8c38b7c6a7f26fe05

https://github.com/suharahiromichi/coq/blob/master/gkp/gkp_4_6_modulo.v
 *)

(* END *)
