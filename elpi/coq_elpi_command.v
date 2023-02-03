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
type inductive    id -> bool -> arity -> (term -> list indc-decl) -> indt-decl.
                      % tt means inductive, ff coinductive
type constructor  id -> arity -> indc-decl.
```
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
## Record

```
kind record-decl type.
type record      id -> term -> id -> record-decl -> indt-decl.
type field       field-attributes -> id -> term -> (term -> record-decl) -> record-decl.
type end-record  record-decl.
```
*)

Elpi hello Record test := { f1 : nat; f2 : bool }.
(**
```
Hello 
[indt-decl
  (record test (sort (typ «Set»)) Build_test 
	(field [coercion off, canonical tt] f1 (global (indt «nat»))  c0 \
       field [coercion off, canonical tt] f2 (global (indt «bool»)) c1 \
       end-record))]
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
Elpi Command defint.
Elpi Accumulate lp:{{
pred int->nat i:int, o:term.
int->nat N {{ 0 }} :- N =< 0, !.
int->nat N {{ S lp:X }} :- M is N - 1, int->nat M X.

main [str Name, int N] :-
  int->nat N Nnat,
  coq.env.add-const Name Nnat {{nat}} _ _,
  coq.locate Name (const Const),
  coq.env.const Const Val Ty,
  coq.say "Const=" Const,
  coq.say "Value=" Val,
  coq.say "Type=" Ty.
}}.
Elpi Typecheck.

Elpi defint one 1.
Print one.                    (* = 1 : nat *)

(**
## Inductive

```
pred coq.env.add-indt i:indt-decl, o:inductive.
pred coq.env.indt-decl i:inductive, o:indt-decl.
```
*)
Inductive test : Set := t1.

Elpi Command defindt.
Elpi Accumulate lp:{{
pred prime i:id, o:id.
  prime S S1 :- S1 is S ^ "'".

main [str Name] :-
  coq.locate Name (indt Indt),
  coq.env.indt-decl Indt Decl,
  Decl = inductive Id Bool Arity (c0 \ [constructor T (arity c0)]),
  coq.say Decl,
  prime Id Id',
  prime T T',
  Decl' = inductive Id' Bool Arity (c0 \ [constructor T' (arity c0)]),
  coq.say Decl',
  std.assert-ok!
      (coq.typecheck-indt-decl Decl')
      "can't be abstracted",
  std.spy (coq.env.add-indt Decl' Indt').
}}.
Elpi Typecheck.

Print test.             (* Inductive test : Set :=  t1 : test. *)
Elpi defindt test.
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
