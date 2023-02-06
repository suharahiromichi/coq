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
Vernacularコマンドというべきかもしれません。

``coq_elpi_hoas.v`` で、Coq項（Gallina項）のHOASの説明をしましたが、
Vernacularコマンドは、Gallina項でないことに注意してください。

これらのコマンドに対するHOASがあるわけではなく、Vernacular コマンド
それぞれにELPIの組込述語が用意されています。
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

Elpi hello 1.           (* Hello [int 1] *)
Elpi hello x.           (* Hello [str x] *)
Elpi hello "y".         (* Hello [str y] *)
Elpi hello z.w.         (* Hello [str z.w] *)

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
Elpi hello Definition test := 0 = 1.
(**
```
Hello 
[const-decl test 
      (some
	      (app [global (indt «eq»),
                  global (indt «nat»),
                  global (indc «O»), 
                  app [global (indc «S»),
                        global (indc «O»)]]))
      (arity (sort prop))]
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
  (inductive windrose
             tt
             (arity (sort (typ «Set»)))
             c0 \
                  [constructor N (arity c0),
                   constructor E (arity c0), 
                   constructor W (arity c0),
                   constructor S (arity c0)])]
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
  (parameter A explicit (sort (typ «Set»))
   c0 \
     inductive tree
             tt
             (arity (sort (typ «Set»)))
             c1 \
                  [constructor leaf (arity c1),
                   constructor node (arity (prod `_` c1 c2 \ prod `_` c0 c3 \ prod `_` c1 c4 \ c1))])]
```
*)

(**
## Record

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
  (record test (sort (typ «Set»)) Build_test 
	(     field [coercion off, canonical tt] f1 (global (indt «nat»))
       c0 \ field [coercion off, canonical tt] f2 (global (indt «bool»))
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
  (parameter A explicit (sort (typ «Set»))
    c0 \
      record test2 (sort (typ «Set»)) Build_test2 
      (     field [coercion off, canonical tt] valid (global (indt «nat»))
       c1 \ field [coercion off, canonical tt] value c0
       c2 \ end-record))]

```
*)

(**
# coq-builtin.elpi

## Constant

```
pred coq.env.add-const i:id, i:term, i:term, i:opaque?, o:constant.
pred coq.env.const i:constant, o:option term, o:term.
```
*)
(**
整数をDefinition するコマンド
*)
Elpi Command defnat_inc.
Elpi Accumulate lp:{{
pred int->nat i:int, o:term.
int->nat N {{ 0 }} :- N =< 0, !.
int->nat N {{ S lp:X }} :- M is N - 1, int->nat M X.

pred nat->int i:term, o:int.
nat->int {{ 0 }} 0.
nat->int {{ S lp:X }} N :- nat->int X M, N is M + 1.

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
Elpi Typecheck.

Definition one := 1.
Elpi defnat_inc one.
Print one.                    (* = 1 : nat *)
Print one'.                   (* = 2 : nat *)

(**
## Inductive

```
pred coq.env.add-indt i:indt-decl, o:inductive.
pred coq.env.indt-decl i:inductive, o:indt-decl.
```
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
# コマンドの例
*)
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
      int->nat N {{ S lp:X }} :- M is N - 1, int->nat M X.

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

(* END *)
