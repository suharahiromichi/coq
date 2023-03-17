
(**
Coq-Elpi によるコマンドの作成 - コマンドの例
=====================

@suharahiromichi

2023/3/18 ProofCafe

ソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/elpi/coq_elpi_command_2.v


以下の説明も参照してください。


https://github.com/suharahiromichi/coq/blob/master/elpi/coq_elpi_command.v
*)

From elpi Require Import elpi.

(**
# コマンドの例
*)
Module Ex4.

(**
## Define と Axiom と Inductive と同じ機能のコマンド - def
*)
Elpi Command def.
Elpi Accumulate lp:{{
  main [const-decl Name (some Decl) (arity Type)] :-
    coq.env.add-const Name Decl Type _ Const,
    coq.say Const "is defined.".
  main [const-decl Name none (arity Type)] :-
    coq.env.add-axiom Name Type Ax,
    coq.say Ax "is defined.".
  main [indt-decl Decl] :-
    coq.env.add-indt Decl Indt,
    coq.say Indt "is defined.".
}}.
Elpi Typecheck.
Elpi def Definition ex1 := 0.
Elpi def Axiom a1 : forall b, b = true.
Elpi def Inductive ex2 : Set := Ex2 : ex2.
Elpi def Inductive ex3 (A : Set) : Set := Ex3 (a : A) : ex3 A.
Print ex1.
Check a1.
Print ex2.
Print ex3.

End Ex4.

(**
## 定義済みの自然数を (+1) した数を定義するコマンド - defnat_inc
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
## 型をコンストラクタにプライム(')をつけるコマンド - defindt_p

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
  coq.env.add-indt Decl' Indt'.
}}.
Elpi Typecheck.

Print test.             (* Inductive test : Set :=  t1 : test. *)
Elpi defindt_p test.
Print test'.            (* Inductive test' : Set :=  t1' : test'. *)

(**
## Coqとしての型をチェックするコマンド - check_arg
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
## (略) elaborate_arg
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
## コンストラクタがいくつあるか調べるコマンド - constructors_num

その数を第2引数で指定した定数で定義する。
*)
Elpi Command constructors_num.
Elpi Accumulate lp:{{
      pred int->nat i:int, o:term.
      int->nat 0 {{ 0 }}.
      int->nat N {{ S lp:{{X}} }} :- M is N - 1, int->nat M X.

      main [str IndName, str Name] :-
            coq.locate IndName (indt GR),
            coq.say "GR=" GR,
            coq.env.indt GR _ _ _ _ Kn _,
            coq.say "Kn=" Kn,
            std.length Kn N,
            coq.say "N=" N,
            int->nat N Nnat,
            coq.say "Nnat=" Nnat,
            coq.env.add-const Name Nnat _ _ _.
      }}.
Elpi Typecheck.

Elpi constructors_num bool nK_bool.       (* 2 *)
Print nK_bool.                            (* nK_bool = 2 : nat *)

Inductive windrose : Set := N | E | W | S.
Elpi constructors_num windrose nK_windrose.
Print nK_windrose.                        (* nK_windrose = 4 : nat *)

(**
## 帰納的定義の一部の抽象する（変数にする）コマンド - abstract
*)
Elpi Command abstract.
Elpi Accumulate lp:{{

  pred prime i:id, o:id.
  prime S S1 :- S1 is S ^ "'".

  main [str Ind, trm Param] :-
    % the term to be abstracted out, P of type PTy
    std.assert-ok!
      (coq.elaborate-skeleton Param PTy P)
      "illtyped parameter",
    
    % Ind で指定された、元の定義を取り出す。
    std.assert! (coq.locate Ind (indt I)) "not an inductive type",
    coq.env.indt-decl I Decl,

    % copy-clauses手法を利用した、object-level abstruction
    % ``P``を``a``にコピーする条件をテンポラリに追加した上で、``Decl``を``Decl' a``にコピー。
    % これにより、Decl' に、Elpiの``λa....``の式が設定される。
    % ``=>``の左辺であるcopyは、copy-indt-decl の中から呼ばれる（注）。
    pi a\ copy P a => copy-indt-decl Decl (Decl' a),

    % パラメータをもつInductiveな定義のために、``parameter`` を追加する。
    NewDecl = parameter "A" explicit PTy Decl',
      
    % Inductiveな定義の全体をprime述語を使用して書き換える。
    coq.rename-indt-decl (=) prime prime NewDecl DeclRenamed,

    % 新しいInductiveな定義の型をチェックする。
    std.assert-ok!
      (coq.typecheck-indt-decl DeclRenamed)
      "can't be abstracted",

    % 新しいInductiveな定義を追加する。
    coq.env.add-indt DeclRenamed A.
}}.
Elpi Typecheck.

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
（注）https://github.com/suharahiromichi/prolog/blob/master/elpi/copy_clauses.elpi

## 補足説明

### copy の定義

```prolog
copy X Y :- name X, !, X = Y, !. % avoid loading "copy x x" at binders
copy (global _ as C) C :- !.
copy (pglobal _ _ as C) C :- !.
copy (sort _ as C) C :- !.
copy (fun N T F) (fun N T1 F1) :- !,
  copy T T1, pi x\ copy (F x) (F1 x).
copy (let N T B F) (let N T1 B1 F1) :- !,
  copy T T1, copy B B1, pi x\ copy (F x) (F1 x).
copy (prod N T F) (prod N T1 F1) :- !,
  copy T T1, (pi x\ copy (F x) (F1 x)).
copy (app L) (app L1) :- !, map L copy L1.
copy (fix N Rno Ty F) (fix N Rno Ty1 F1) :- !,
  copy Ty Ty1, pi x\ copy (F x) (F1 x).
copy (match T Rty B) (match T1 Rty1 B1) :- !,
  copy T T1, copy Rty Rty1, map B copy B1.
copy (primitive _ as C) C :- !.
copy (uvar M L as X) W :- var X, !, map L copy L1, coq.mk-app-uvar M L1 W.
copy (uvar X L) (uvar X L1) :- map L copy L1.
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

(* END *)
