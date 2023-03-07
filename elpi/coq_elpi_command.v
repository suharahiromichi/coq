
(**
Coq-Elpi によるコマンドの作成
=====================

@suharahiromichi

2023/2/4

2023/2/18 ProofCafe
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

(**
# コマンドの例
*)
Module Ex4.

(**
## Define と Inductive と同じ機能のコマンド
*)
Elpi Command def.
Elpi Accumulate lp:{{
      main [const-decl Name (some Decl) (arity Type)] :-
        coq.env.add-const Name Decl Type _ Const,
        coq.say Const "is defined.".
      main [indt-decl Decl] :-
        coq.env.add-indt Decl Indt,
        coq.say Indt "is defined.".
}}.
Elpi Typecheck.
Elpi def Definition ex1 := 0.
Elpi def Inductive ex2 : Set := Ex2 : ex2.
Elpi def Inductive ex3 (A : Set) : Set := Ex3 (a : A) : ex3 A.
Print ex1.
Print ex2.
Print ex3.

End Ex4.

(**
## 定義済みの自然数を (+1) した数を定義するコマンド
*)
Elpi Command defnat_inc.
Elpi Accumulate lp:{{
pred int->nat i:int, o:term.
int->nat N {{ 0 }} :- N =< 0, !.
int->nat N {{ S lp:{{X}} }} :- M is N - 1, int->nat M X.

pred nat->int i:term, o:int.
nat->int {{ 0 }} 0.
nat->int {{ S lp:{{X}} }} N :- nat->int X M, N is M + 1.

pred prime i:id, o:id.
prime S S1 :- S1 is S ^ "'".

main [str Name] :-
coq.locate Name (const Const),
  coq.env.const Const (some Nnat) {{nat}},
  nat->int Nnat N,
  prime Name Name1,
  N1 is N + 1,
  int->nat N1 Nnat1,
  coq.env.add-const Name1 Nnat1 {{nat}} _ _.
}}.
(**
``lp:{{X}}`` は ``lp:X`` でよいはずだが、vscodeからではうまくいなない。
*)

Elpi Typecheck.

Definition one := 1.
Elpi defnat_inc one.
Print one.                    (* = 1 : nat *)
Print one'.                   (* = 2 : nat *)

(**
## 型をコンストラクタにプライム(')をつけるコマンド

coq.rename-indt-decl のほうが容易だが、
ここでは、定義をしなおしてみる。
*)
Inductive test : Set := t1.

Elpi Command defindt_p.
Elpi Accumulate lp:{{
pred prime i:id, o:id.
  prime S S1 :- S1 is S ^ "'".

main [str Name] :-
  coq.locate Name (indt Indt),
  coq.env.indt-decl Indt Decl,
  Decl = inductive Idt Bool Arity (c0 \ [constructor Idc (arity c0)]),
  coq.say Decl,
  prime Idt Idt',
  prime Idc Idc',
  Decl' = inductive Idt' Bool Arity (c0 \ [constructor Idc' (arity c0)]),
  coq.say Decl',
  std.assert-ok!
      (coq.typecheck-indt-decl Decl')
      "can't be abstracted",
  std.spy (coq.env.add-indt Decl' Indt').
}}.
Elpi Typecheck.

Print test.             (* Inductive test : Set :=  t1 : test. *)
Elpi defindt_p test.
Print test'.            (* Inductive test' : Set :=  t1' : test'. *)

(**
## check_arg コマンド
*)
Elpi Command check_arg.
Elpi Accumulate lp:{{
      main [trm T] :-
            std.assert-ok! (coq.typecheck T Ty) "argument illtyped",
            coq.say "The type of" T "is" Ty.
}}.
Elpi Typecheck.

Elpi check_arg (1 = 0).
(**
```
The type of 
app [global (indt «eq»),
     global (indt «nat»), 
     app [global (indc «S»), global (indc «O»)],
     global (indc «O»)]
is
sort prop
```
*)

Fail Check (1 = true).
Fail Elpi check_arg (1 = true).  (* fails *)
(**
```
The command has indeed failed with message:
(略)
```
*)

(**
コアーションも適用されるようになった。
 *)
Coercion bool2nat (b : bool) := if b then 1 else 0.
Check (1 = true).
Elpi check_arg (1 = true).

(**
## elaborate_arg コマンド
*)
Elpi Command elaborate_arg.
Elpi Accumulate lp:{{
      main [trm T] :-
            std.assert-ok! (coq.elaborate-skeleton T Ty T1) "illtyped arg",
            coq.say "T=" T,
            coq.say "T1=" T1,
            coq.say "Ty=" Ty.
      }}.
Elpi Typecheck.

Elpi elaborate_arg (1 = true).
(**
Tですでにコアーションが適用されるようになったため、
エラボレーション結果のT1と等しくなってしまう。

```
T= app [global (indt «eq»),
      global (indt «nat»), 
      app [global (indc «S»), global (indc «O»)], 
      app [global (const «bool2nat»), global (indc «true»)]]

T1= app [global (indt «eq»),
      global (indt «nat»), 
      app [global (indc «S»), global (indc «O»)], 
      app [global (const «bool2nat»), global (indc «true»)]]

Ty= sort prop
```
*)

(**
## constructors_num コマンド
*)
Elpi Command constructors_num.
Elpi Accumulate lp:{{
      pred int->nat i:int, o:term.
      int->nat 0 {{ 0 }}.
      int->nat N {{ S lp:{{X}} }} :- M is N - 1, int->nat M X.

      main [str IndName, str Name] :-
            coq.say "IndName=" IndName,
            coq.locate IndName (indt GR),
            coq.say "GR=" GR,
            coq.env.indt GR _ _ _ _ Kn _,
            coq.say "Kn=" Kn,
            std.length Kn N,
            coq.say "N=" N,
            int->nat N Nnat,
            coq.say "Nnat=" Nnat,
            coq.say "Name=" Name,
            coq.env.add-const Name Nnat _ _ _.
      }}.
Elpi Typecheck.

Elpi constructors_num bool nK_bool.       (* 2 *)
Print nK_bool.                            (* nK_bool = 2 : nat *)

Inductive windrose : Set := N | E | W | S.
Elpi constructors_num windrose nK_windrose.
Print nK_windrose.                        (* nK_windrose = 4 : nat *)

(**
# 補足説明
*)

(* 以下は同じ結果になる。matchのリストは、コンストラクタの順番に並ぶ。 *)
Elpi hello (fun x => match x with | N => 0 | E => 1 | S => 4 | _ => 3 end).
Elpi hello (fun x => match x with | W => 3 | E => 1 | S => 4 | _ => 0 end).

(* match はふたつであり、そのネストになる。natのコンストラクタはふたつである。 *)
Elpi hello (fun n => match n with | 0 => 0 | 1 => 2 | _ => 3 end).

(**
# 帰納的定義を抽象化するコマンド

HOASの一部を書き換えるにはどうするか、の例である。
*)
Elpi Command abstract.
Elpi Accumulate lp:{{
  pred prime i:id, o:id.
  prime S S1 :- S1 is S ^ "'".

    main [str Ind, trm Param] :-
    std.spy (std.assert-ok!
      (coq.elaborate-skeleton Param PTy P)
      "illtyped parameter"),
    std.assert! (coq.locate Ind (indt I)) "not an inductive type",
    std.spy (coq.env.indt-decl I Decl),

    (pi a\ copy P a => std.spy (copy-indt-decl Decl (Decl' a))),
%   Decl'' = (Decl' a),                     % ここを　Decl''   で受けることはできないらしい。
%   coq.say "Decl''=" Decl'',
%   coq.say "Decl'=" Decl',

    % coq-lib.elpi で定義されている copy-indt-decl は、arity の T のコピーに copy を使う。
    % ``copy P a`` を前提に置いて、copy-indt-decl を実行する。
    % ``=>``の左辺であるcopyは、copy-indt-decl の中から呼ばれる。

    % 第1引数で指定された、Inductive定義を parameter で包む。
    % オリジナルでは、ひとつまえの場所だったが、この場所でも支障ない。
    % ただし、Decl` は、引数をとるラムダ式になる。
    std.spy (NewDecl = parameter "A" explicit PTy Decl'),

    % 名前に``'``を付けて定義する。この説明は省略する。
    std.spy (coq.rename-indt-decl (=) prime prime NewDecl DeclRenamed),
    std.assert-ok!
      (coq.typecheck-indt-decl DeclRenamed)
      "can't be abstracted",
    std.spy (coq.env.add-indt DeclRenamed A).
}}.
Elpi Typecheck.

(**
## 実行例
*)
Inductive tree :=
| leaf
| node : tree -> option nat -> tree -> tree.
Print tree.
(**
```
Inductive tree : Set :=
|	leaf : tree 
| node : tree -> option nat -> tree -> tree.
```
*)
(**
tree の option nat が A に置き換わる。
*)
Elpi abstract tree (option nat).
Print tree'.
(**
```
Inductive tree' (A : Set) : Set :=
|	leaf' : tree' A 
| node' : tree' A -> A -> tree' A -> tree' A.
```
*)

(**
## 補足説明

### copy の定義

```prolog

copy X X :- name X.      % checks X is a bound variable
copy (global _ as C) C.
copy (fun N T F) (fun N T1 F1) :-
    copy T T1, pi x\ copy (F x) (F1 x).
copy (app L) (app L1) :- std.map L copy L1.
```

### ``copy P a`` の意味

以下が、上記のcopyの定義に優先して使われる。

```prolog
copy (app [global (indt «option»), global (indt «nat»)]) c0.
```

### copy-indt-decl

定義

```
pred copy-indt-decl i:indt-decl, o:indt-decl.
copy-indt-decl (parameter ID I Ty D) (parameter ID I Ty1 D1) :-
  copy Ty Ty1,
  @pi-parameter ID Ty1 x\ copy-indt-decl (D x) (D1 x).
copy-indt-decl (inductive ID CO A D) (inductive ID CO A1 D1) :-
  copy-arity A A1,
  @pi-inductive ID A1 i\ std.map (D i) copy-constructor (D1 i).
copy-indt-decl (record ID T IDK F) (record ID T1 IDK F1) :-
  copy T T1,
  copy-fields F F1.
```

copy-indt-declの実行結果は、以下である。
``(app [global (indt «option»), global (indt «nat»)])``
の部分を変数``c0``に置き換えながら copy したのが解る。

```
copy-indt-decl
 (inductive tree tt (arity (sort (typ «Set»))) c1 \
   [constructor leaf (arity c1), 
  	constructor node 
     (arity (prod `_` c1 c2 \ prod `_` (app [global (indt «option»), global (indt «nat»)]) 
                         c3 \ prod `_` c1 c4 \ c1))]) 
 (inductive tree tt (arity (sort (typ «Set»))) c1 \
   [constructor leaf (arity c1), 
    constructor node 
     (arity (prod `_` c1 c2 \ prod `_` c0
                         c3 \ prod `_` c1 c4 \ c1))])
```
*)
<
(* END *)
