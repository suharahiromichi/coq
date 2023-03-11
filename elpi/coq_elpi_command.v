
(**
Coq-Elpi によるコマンドの作成
=====================

@suharahiromichi

2023/2/4

2023/2/18 ProofCafe

2023/3/18 ProofCafe   後半のコマンド例を分離した。


ソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/elpi/coq_elpi_command.v
*)

(**
# はじめに

ELPIでCoqのコマンドを作成してみます。
ここでのコマンドは Definition や Inductive などの
Vernacularコマンドということもありますが、ここではCoqコマンドで統一します。

``coq_elpi_hoas.v`` で、Coq項（Gallina項）のHOASの説明をしましたが、
Vernacularコマンドは、Gallina項でないことに注意してください。

これらのコマンドに対するHOASがあるわけではなく、Vernacular コマンド
それぞれにに対応するコンストラクタやELPIの組込述語が用意されています。

すこし紛らしいのですは、今回は次の順番で説明をします。

1. Coqコマンド全体を示す、Elpiのコンストラクタ

2. Coqコマンドで定義した内容を取り出すElpiの組込述語

3. Coqコマンドと同じ機能のElpiの組込述語
*)
From elpi Require Import elpi.

(**
# hello コマンド
*)
Elpi Command hello.
Elpi Accumulate lp:{{
      /* main is, well, the entry point */
      main Arguments :- coq.say "Hello" Arguments.
}}.
Elpi Typecheck.

(**
# Command の引数

## 整数と文字列とCoq項

Command の ``main`` の引数 ``Arguments`` の型は、``list argument`` である。

HOASのチュートリアルでみた``term``型以外にも、整数や文字列を渡すことができる。

```
kind argument type.
type int       int    -> argument.
type str       string -> argument.
type trm       term   -> argument.
```
*)

Elpi hello 0.           (* Hello [int 0] *)
Elpi hello x.           (* Hello [str x] *)
Elpi hello "y".         (* Hello [str y] *)
Elpi hello z.w.         (* Hello [str z.w] *)
Elpi hello 0 1 x y z.
(* Coq項を渡すには、括弧で囲むこと。 *)
Elpi hello (0).         (* Hello [trm (global (indc «O»))] *)
Elpi hello (nat).
Fail Elpi hello (f).    (* fは未定義 *)

(**
注意：

ここでは、hello の出力結果をコピーペーストしているが、
これをコードに貼り付ける場合は、constantなどの「«»」で囲まれたトークンは書けないこと、
hello の出力では、id (string) の引用符「""」が消えていることに、注意すること。
*)


(**
## Coqの命令

Define や Inductive の命令は、ぞれ全体ではCoq項ではないので、
それを渡すために、特別なコンストラクタがある。

### Defininition

```
type const-decl   id -> option term -> arity -> argument.
type arity        term -> arity.
```
*)
Elpi hello Definition test := 0.
(**
```
Hello 
[const-decl test
      (some (global (indc «O»)))
      (arity (global (indt «nat»)))]
```
*)

(**
## Inductive

```
kind indt-decl type.
kind indc-decl type.
type indt-decl    indt-decl -> argument.
type parameter    id -> implicit_kind -> term -> (term -> indt-decl) -> indt-decl.
%                                                  　　　　↑ inductive .....
type inductive    id -> bool -> arity -> (term -> list indc-decl) -> indt-decl.
                      % tt means inductive, ff coinductive
type constructor  id -> arity -> indc-decl.
```
*)

(**
### 型引数を持たない場合
*)
Elpi hello Inductive windrose : Set := N | E | W | S.
(**
```
Hello 
[indt-decl
  (inductive "windrose"
             tt
             (arity (sort (typ «Set»)))
             c0 \
                  [constructor "N" (arity c0),
                   constructor "E" (arity c0), 
                   constructor "W" (arity c0),
                   constructor "S" (arity c0)])]
```
*)

(**
### 型引数を持つ場合
*)
Elpi hello Inductive tree (A : Set) : Set := leaf : tree A | node : tree A -> A -> tree A -> tree A.
(**
```
Hello 
[indt-decl
  (parameter "A" explicit (sort (typ «Set»))
   c0 \
     inductive tree
             tt
             (arity (sort (typ «Set»)))
             c1 \
                  [constructor "leaf" (arity c1),
                   constructor "node" (arity (prod `_` c1 c2 \ prod `_` c0 c3 \ prod `_` c1 c4 \ c1))])]
```
*)

(**
## Record

Recored　は Inductive な定義に変換できるが、Coqコマンドのレベルでは、変換せずに定義される

Coqコマンドの Recored と Structure のどちらでも、同じようにrecord コンストラクタが使われる。


```
kind record-decl type.
type record      id -> term -> id -> record-decl -> indt-decl.
type field       field-attributes -> id -> term -> (term -> record-decl) -> record-decl.
type end-record  record-decl.
```
*)

(**
### 型引数を持たない場合
*)
Elpi hello Record test := { f1 : nat; f2 : bool }.
(**
```
Hello 
[indt-decl
  (record "test" (sort (typ «Set»)) "Build_test"
	(     field [coercion off, canonical tt] "f1" (global (indt «nat»))
        c0 \ field [coercion off, canonical tt] "f2" (global (indt «bool»))
             c1 \ end-record))]
```
*)

(**
### 型引数を持つ場合

Structure でも Record でも同じ。
*)
Elpi hello Structure test2 (A : Set) := { valid : nat; value : A }.
(**
```
Hello 
[indt-decl
  (parameter "A" explicit (sort (typ «Set»))
    c0 \
      record "test2" (sort (typ «Set»)) "Build_test2"
      (     field [coercion off, canonical tt] "valid" (global (indt «nat»))
       c1 \ field [coercion off, canonical tt] "value" c0
       c2 \ end-record))]

```
*)

(**
# coq-builtin.elpi

以下では、Elpiから Coq　の Definition や Inductive コマンドに相当することを実行してみます。

## Constant (Definition)

```
pred coq.env.add-const i:id, i:term, i:term, i:opaque?, o:constant.
pred coq.env.const i:constant, o:option term, o:term.
```
*)

(** 例は練習問題 *)

(**
## Inductive

```
pred coq.env.add-indt i:indt-decl, o:inductive.
pred coq.env.indt-decl i:inductive, o:indt-decl.
```
*)

(** 例は練習問題 *)

(**
# 練習問題 1.

hello を使用して、以下のコマンド全体を出力してください。

1. ``Definition ex1 := 1``

2. ``Inductive ex2 : Set := Ex2 : ex2``

3. ``Inductive ex3 (A : Set) : Set := Ex3 : ex3 A``
*)

Elpi hello Definition ex1 := 1.
(**
出力：
```
[const-decl ex1 
  (some (app [global (indc «Datatypes.S»), global (indc «O»)])) 
  (arity (global (indt «nat»)))]
```
*)

Elpi hello Inductive ex2 : Set := Ex2 : ex2.
(**
出力：
```
[indt-decl
  (inductive ex2 tt (arity (sort (typ «Set»)))
   c0 \	[constructor Ex2 (arity c0)])]
```
*)

Elpi hello Inductive ex3 (A : Set) : Set := Ex3 : A -> ex3 A.
(**
出力：
```
Hello 
[indt-decl
  (parameter A explicit sort (typ «Set»)) 
    c0 \ inductive ex3 tt (arity (sort (typ «Set»))) 
     c1 \ [constructor Ex3 (arity (prod `_` c0 c2 \ c1))])]
```
*)

(**
# 練習問題 2.1

1. constant の内容をPrintするコマンドを定義してくだい。

2. 帰納型の内容をPrintするコマンドを定義してくだい。
*)

Elpi Command PrintConst.
Elpi Accumulate lp:{{
main [str Name] :-
coq.locate Name (const Const),
  coq.env.const Const (some Bo) Ty,
  coq.say "Body=" Bo,
  coq.say "Type=" Ty.
}}.
Elpi Typecheck.

Elpi Command PrintInductive.
Elpi Accumulate lp:{{
main [str Name] :-
  coq.locate Name (indt Indt),
  coq.env.indt-decl Indt Decl,
  coq.say "Indt=" Indt,
  coq.say "Decl=" Decl.
}}.
Elpi Typecheck.

(**
# 練習問題 2.2

以下の ex1, ex2, ex3 を上のコマンドでPrintしてください。
*)
Module Ex2.
  Definition ex1 := 0.
  Inductive ex2 : Set := Ex2 : ex2.
  Inductive ex3 (A : Set) : Set := Ex3 (a : A) : ex3 A.

  Elpi PrintConst "ex1".
(**
出力：
```
global (indc «O»)
```
*)
Elpi PrintInductive "ex2".
(**
出力：
```
inductive ex2 tt (arity (sort (typ «Set»)))
 c0 \ [constructor Ex2 (arity c0)]
```
 *)
Elpi PrintInductive "ex3".
(**
出力：
```
[indt-decl
  (parameter A explicit (sort (typ «Set»)) 
    c0 \ inductive ex3 tt (arity (sort (typ «Set»))) 
      c1 \ [constructor Ex3 (arity (prod `_` c0 c2 \ c1))])]
```
*)
End Ex2.

(**
# 練習問題 3

1. ``Definition ex1 := 1`` と同じコマンドを定義してくだい。

2. ``Inductive ex2 : Set := Ex2 : ex2`` と同じコマンドを定義してください。

3. ``Inductive ex3 (A : Set) : Set := Ex3 (a : A) : ex3 A`` と同じコマンドを定義してください。

練習問題2 の結果を使う場合は、constantなどの「«»」で囲まれたトークンは書けないこと、
hello の出力では、id (string) の引用符「""」が消えていることに、注意すること。
*)

(**
## (1) ``Definition ex1 := 0`` と同じコマンド。
*)
Module Ex3.
Elpi Command Ex1.
Elpi Accumulate lp:{{
main [] :-
coq.env.add-const "ex1" {{0}} {{nat}} _ Const,
  coq.env.const Const (some Bo) Ty,
  coq.say "Bo=" Bo,
  coq.say "Ty=" Ty.
}}.
Elpi Typecheck.
Elpi Ex1.
Check ex1.

(**
## (2) ``Inductive ex2 : Set := Ex2 : ex2`` と同じコマンド。
*)
Elpi Command Ex2.
Elpi Accumulate lp:{{
main [] :-
coq.env.add-indt
  (inductive "ex2" tt (arity {{Set}})
   c0 \ [constructor "Ex2" (arity c0)])
   Indt,
coq.env.indt-decl Indt Bo,
coq.say "Bo=" Bo.
}}.
Elpi Typecheck.
Elpi Ex2.
Print ex2.

(**
## (3) ``Inductive ex3 (A : Set) : Set := Ex3 (a : A) : ex3 A`` と同じコマンド。
*)
Elpi Command Ex3.
Elpi Accumulate lp:{{
main [] :-
  coq.env.add-indt
      (parameter "A" explicit {{Set}}
        c0 \ (inductive "ex3" tt (arity {{Set}})
             c1 \ [constructor "Ex3" (arity (prod `a` c0 c2 \ c1))]))
      Indt,
% coq.locate "ex3" (indt Indt),
  coq.env.indt-decl Indt Bo,
  coq.say "Bo=" Bo.
}}.
Elpi Typecheck.
Elpi Ex3.
Print Ex3.

End Ex3.

(* END *)
