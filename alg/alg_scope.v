(**
Scope について
=======

2023_10_29 @suharahiromichi
 *)
From elpi Require Import elpi.              (* coq-elpi *)
From HB Require Import structures.          (* coq-hierarchy-builder. *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_field.     (* 必要な場合のみ *)

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

(**
通常はここで、ring_scope を open しますが、ここでは説明のため、あとで行います。
*)
(* Open Scope ring_scope. *)

(**
# 概説

2項演算子などのNotation は、必ず scope に依存します。
scopeが決まらないとNotationの解釈は決まりません。

scopeを決める方法には、以下の方法があります。

- ``Open Scope`` コマンドでscopeを指定して、大局的に切り替える方法
ある演算子が複数のscopeで定義されている場合、あとでopneされたscopeが優先されます。
Locateコマンドで調べると、``default interpretation`` として表示されます。

- 項を Demliter で囲む方法
項を単位としてスコープを指定します。デリミタはのスコープ名に対して短いニモニックが決められています。

- 型アノテーションを使う方法

以降、順番に説明します。
*)

(**
# Scopeとはなにか

以下に、それぞれのScopeと意味、およびデミリタを示します。


|優先度| scope    | Delimiter  |  意味         | open済  |
|:---|:---------|:-----------|:--------------|:------:|
| 小 | core_scope | なし     |               | ○ |
| ↑  | type_scope | %type     | 型、Prop      | ○ |
|    | bool_scope | %B        |               | ○ |
|    | nat_scope  | %N        |               | ○ |
|    | fun_scope  | %FUN      |               | ○ |
| ↓  | pair_scope | %PAIR     |               | ○ |
| 大 | seq_scope  | %SEQ      |               | ○ |
|    | coq_nat_scope | %coq_nat | Standar Coq の nat | × |
|    | order_scope | %O       |               | × |
|    | big_scope  | %BIG      |               | × |
|    | ring_scope | %R        |               | × |
|    | int_scope  | %Z        |               | × |
|    | distn_scope |          | (本文参照)    | × |
|    | rat_scope  | %Q        |               | × |
|    | matrix_set_scope | %MS | matrix        | × |
|    | vspace_scope     | %VS | vector        | × |
|    | C_scope          | %C  | complex       | × |

優先順位は、あとで指定したものから優先されます。
 *)

(**
# 2項演算子

Locate コマンドを使うと演算子の定義と、依存するscopeの対応が分かります。
このとき、「nat_scope で定義された演算子``+``」というような言い方をします。

2項演算子の一部について、抜粋してみます。
 *)
Locate "_ : _ ".
(**
```
Notation "x : T" := (x : T) : core_scope (default interpretation)
```
 *)
Locate "_ /\ _".
(**
```
Notation "A /\ B" := (and A B) : type_scope (default interpretation)
```
 *)
Locate "_ && _".
(**
```
Notation "x && y" := (andb x y) : bool_scope (default interpretation)
```
*)
Locate "_ + _".
(**
```
Notation "m + n" := (Nat.add m n) : coq_nat_scope
Notation "A + B" := (addsmx.body A B) : matrix_set_scope
Notation "m + n" := (addn m n) : nat_scope (default interpretation)
Notation "x + y" := (addq x y) : rat_scope
Notation "x + y" := (GRing.add x y) : ring_scope
Notation "x + y" := (sum x y) : type_scope
Notation "U + V" := (addv U V) : vspace_scope
```
*)
Locate "_ - _".
(**
```
Notation "m - n" := (Nat.sub m n) : coq_nat_scope
Notation "m - n" := (GRing.add (m : int) (GRing.opp (n : int))) : distn_scope
Notation "m - n" := (subn m n) : nat_scope (default interpretation)
Notation "x - y" := (subq x y) : rat_scope
Notation "x - y" := (GRing.add x (GRing.opp y)) : ring_scope
```
*)
Locate "_ * _".
(**
```
Notation "m * n" := (Nat.mul m n) : coq_nat_scope
Notation "R * S" := (mulsmx R S) : matrix_set_scope
Notation "m * n" := (muln m n) : nat_scope (default interpretation)
Notation "x * y" := (mulq x y) : rat_scope
Notation "x * y" := (GRing.mul x y) : ring_scope
Notation "x * y" := (prod x y) : type_scope
Notation "A * B" := (prodv A B) : vspace_scope
```
*)
Locate "_ %/ _".
(**
```
Notation "x %/ y" := (divz x y) : int_scope
Notation "m %/ d" := (divn m d) : nat_scope (default interpretation)
Notation "m %/ d" := (divp m d) : ring_scope
```
*)
Locate "_ / _".
(**
```
Notation "x / y" := (divq x y) : rat_scope
Notation "x / y" := (GRing.mul x (GRing.inv y)) : ring_scope
```
*)
Locate "_ <= _".
(**
```
Notation "m <= n" := (le m n) : coq_nat_scope
Notation "A <= B" := (submx.body A B) : matrix_set_scope
Notation "m <= n" := (leq m n) : nat_scope (default interpretation)
Notation "x <= y" := (Order.le x y) : order_scope
Notation "x <= y" := (Order.le x y) : ring_scope
Notation "U <= V" := (subsetv U V) : vspace_scope
```
 *)
Locate "_ \o _".
(**
```
Notation "f1 \o f2" := (comp f1 f2) : fun_scope (default interpretation)
```
*)
Locate "_ .1".
(**
```
Notation "p .1" := (fst p) : pair_scope (default interpretation)
```
*)
Locate "_ :: _".
(**
```
Notation "x :: y" := (cons x y) : list_scope
Notation "x :: y" := (cons x y) : seq_scope (default interpretation)
```
*)
Locate "\big [ _ / _ ]_ ( _ <= _ < _ ) _".
(**
```
Notation "\big [ op / idx ]_ ( m <= i < n ) F" :=
  (bigop.body idx (index_iota m n) (fun i : nat => BigBody i op true F)) : big_scope
  (default interpretation)
```
*)

(**
演算子に対して使いたいNotationが``(default interpretation)`` になっている場合は、
とくに、Notationがひとつしかない場合は、その演算子の使用に問題はありません。

問題は、ひとつの演算子に対して複数のNotationがある場合です。algebraの導入以前にも、
以下の2点で問題になていました。

1. 四則演算子の``+``や``*``は、数の演算ではなく、型の直和や直積の意味でも使われます。
そのtype_scopeの優先度はnat_scopeよりも低いので、デリミタ(``%type``)の指定が必要となります。

2. Stadnard Coqのnatのタクティクを使う場合、Stadnard Coqのnatのscopeの演算子が必要になります。
これもデリミタ(``%coq_nat``)が必要になります。なお、デリミタは変換をやってくれるわけではないので、
適切な補題によるrewriteを行います。

algebra


自然数、環一般、整数、ベクタ、マトリクスで切り替える必要があるほか、
型の直和の意味でも使われます。型の場合は
同様に``*``は、型の直積に意味でも使われるので、その場合はデミリタ(``%type``)の指定が必要となります。

*)

(**
# ``Open Scope`` コマンドの利用

Scope の指定はあと勝ちなので、``Open Scope`` コマンドでscopeを指定すると、
そのscopeが大域的に他のscopeよりも優先されるようになります。
これの影響は大きいため、ring_scope のみに限定するのが習慣のようです。
*)
Open Scope ring_scope.

(**
それでも、四則演算子や大小比較の演算子の ``(default interpretation)`` が、nat_scope
から ring_scope に移ることから、影響は大きいです。
このことに慣れるのが、algebraを克服するポイントのようです。
 *)

(**
# 重大な注意

本題に入るまえに重大な注意をします。scopeはNotation（演算子）だけに効果があります。
単なる変数はには、``Open Scope``コマンドもデミリタもなんの影響を示しません。

むしろ、0、1、42という数値は、nat_scopeで定義されたNotationであることを思い出してください。
 *)
Section Test1.
  Variable n : nat.

  Check n.                                  (* nat *)
  Check n%N.                                (* nat *)
  Check n%R.                                (* nat *)
  Check n%Z.                                (* nat *)
End Test1.

(**
# ゼロへのデリミタの使用

## "0" とは

``0%N`` や ``0%Z`` を考えるまえに、``0``自体について考えてみます。

``0`` は、ring_scope では、
 *)
Locate "0".
(**
```
Notation "0" := GRing.zero : ring_scope (default interpretation)
Notation "0" := (vline GRing.zero) : vspace_scope
```
であり、nmodType型の型をとり、その零元を返す関数です。
 *)
Check @GRing.zero : forall s : nmodType, s.

(**
最初に、半環Sを定義して、それを与えてみます。SはnmodTypeであるので、指定できます。
明示的に半環Sを指定しても、文脈から補完できてもよいわけです。
ring_socpe のなかで、デミリタを使わずにこれができているわけです。
*)
Section Test2.
  Variable S : semiRingType.

  Check S : nmodType.
  Check 0 : S.
  Check GRing.zero : S.
  Check @GRing.zero S.                      (* S *)
End Test2.

(**
int も nmodType であるので、GRing.zero の第1引数にint を指定することができます。
*)
Check int : nmodType.
Check 0 : int.
Check @GRing.zero int.                      (* int *)

(**
rat_scope の ``%Q``も指定できます。
*)
Check rat : nmodType.
Check 0 : rat.
Check @GRing.zero rat.                      (* rat *)

(**
nat さえも同様です。
*)
Check 0 : nat.
Check 0%N.                                  (* nat *)
Check @GRing.zero nat.                      (* nat *)

(**
## ゼロへのデミリタの使用

わざわざ説明しましたが、ゼロへのデミリタの使用は、このメカニズムではありません。
単に自然数の``0``、すなわち``O``からのコアーションです。
*)
Check 0%Z.                                  (* int *)
Check Posz 0.                               (* int *)

Check 0%Q.                                  (* rat *)
Check @Rat (@pair int int (Posz O) (Posz (S O))) (fracq_subproof (@pair int int (Posz O) (Posz (S O)))).
Check Rat (fracq_subproof (pair (Posz O) (Posz (S O)))). (* 分母を非零にして ``0/1`` *)
(**
当然、以下のようになります。
*)
Check 0%N.                                  (* nat *)
Check O.                                    (* nat *)

(**
# 項へのデミリタの使用

つぎに ``0 + 0`` にデミリタを適用することを考えます。

文脈からsemiRingTypeの型のS型と判れば、addは型S上の足し算と解ります。
*)
Section Test3.
  Variable S : semiRingType.
  
  Check 0 + 0 : S.
  Check @GRing.add S (@GRing.zero S) (@GRing.zero S). (* S *)
End Test3.

(**
しかし、int_scopeに``+``はないため、nmodType型の型までしか型は決まりません。
*)
Check (0 + 0)%Z.                            (* (_ : nmodType) *)
(**
むしろ、``0``のほうにデミリタをつけたほうが、効果的です。
*)
Check 0%Z + 0%Z.                            (* int *)

(**
以上からデミリタは乱用せず、補助的につかうのがよいようです。
*)

(**
# 型変換演算子

デミリタとよく似たものに ``%:Z``のような、型変換演算子があります。
これらは、該当箇所で実際に処理をおこなって変換するので、誤解がすくないと思われす。
多項式型など、デミリタにない型への変換もあります。
 *)
Locate "%:R".
(* Notation "n %:R" := (GRing.natmul (GRing.one _) n) : ring_scope (default interpretation) *)
Check (fun (n : nat) => (GRing.one _) *+ n) : nat -> (_ : semiRingType).

Locate "%:Z".
(* Notation "n %:Z" := (Posz n) : int_scope *)
Check Posz : nat -> int.

Locate "%:Q".
(* Notation "n %:Q" := (intmul (GRing.one _) (n : int) : rat) : ring_scope (default interpretation) *)
Check (fun (n : int) => (intmul (GRing.one _) (n : int) : rat)) : int -> rat.

Locate "%:P".
(* Notation "c %:P" := (polyC c) : ring_scope (default interpretation) *)
Check polyC : (_ : semiRingType) -> {poly (_ : semiRingType)}.

(**
# 等式の型の指定

``=`` も ``==``  も暗黙の第1引数に両辺の型を指定していたことを思い出してください。
``_ = _ :> _`` のかたちで第1引数を指定できます。ここのは（デミリタでなく）型を書きます。

等式を使った証明の場合は、この表記を積極的に採用するのがよいのではないかと
ただし、CoqのGoalの表示では、``:>``以降が消されてしまうので、コメントやCheckで補うとよいといでしょう。
*)

Check 0 = 0 :> int.
Check @eq int (Posz O) (Posz O).

Check 0 = 0 :> rat.
Check @eq rat (@GRing.zero rat) (@GRing.zero rat).

(**
# 補足説明
*)
Check @GRing.zero : forall s : nmodType, s.
(**
上記の``:``の右は型なので、任意のnmodType型の値を返す、と誤解しないでください。

また、GRing.zero は関数であるため、GRing.zero を（Notation経由ではなく）
直接呼び出している限り、``Open Scope``コマンドや、デミリタの影響をうけません。
*)
Check @GRing.zero%Z : forall s : nmodType, s.
Check (@GRing.zero int)%Q : int.

(**
# まだ説明していないこと

term_scope
*)

(* END *)
