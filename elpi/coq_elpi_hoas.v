(**
Coq-Elpi Coq項のHOASについて
=====================

@suharahiromichi

2023/1/30

2023/2/18 ProofCafe



https://qiita.com/suharahiromichi/private/23ecf3c91204d43a8b81

https://github.com/suharahiromichi/coq/blob/master/elpi/coq_elpi_hoas.v

この文書は、

Coq項のHOASについてのチュートリアル

https://qiita.com/suharahiromichi/private/62359119f7f880f94d48

からの抜粋である。
*)

(**
# はじめに

Coqの項を抽象構文木で扱う方法を勉強します。Coqの項（Gallina項と呼ぶ場合もありますが、
ここでは、Coq項で統一します）は、ELPIからみて、``term``型のデータです。

Coq項、それが型を表すものであっても、値を表すものであっても、``term``であることに違いがありません。
Coq項なので、Coqとして解釈した場合の「型」は当然ありますが、それは1階上の話になるわけです。

Coqの文法を復習してみます。Coq項の構文木の「葉」になるのは、以下のものです。

- ``Define`` や ``Inductive`` で定義されたもの。global reference と呼ばれる。
  - constant
  - inductive type
  - inductive constructor

Moduleの中で定義された場合でも、Module名を前に付けてグローバルに定義されているとします。


- Coqにあらかじめ用意されている型 (ソート)
  - Proop
  - Set
  - Type

これらは定義できませんが、``Type``は内部的には、``Type_i``のレベルi（階層）を持っています。
*)

From elpi Require Import elpi.

Elpi Command tutorial_HOAS.

(**
# Global refernce

## 定義

```
kind gref       type.
type const      constant -> gref.
type indt       inductive -> gref.
type indc       constructor -> gref.

kind term       type.
type global     gref -> term.
```
*)

(**
|id       | (‡)  　　　  | gref      | gref         | term               | term       |
|:--------|:-----------|:-----------|:-------------|:-------------------|:-----------|
|"Nat.add"| «Nat.add»  |const «Nat.add» |{{:gref Nat.add}} | global (indt «Nat.add»)| {{Nat.add}}    |
| "nat"   | «nat»      |indt «nat»  |{{:gref nat}} | global (indt «nat»)| {{nat}}    |
| "O"     | «O»        |indc «O»    |{{:gref O}}   | global (indc «O»)  | {{O}}      |



(‡) constant, inductive, constructor

``{{ ... }}`` は ``{{:coq ... }}`` の略。
*)

(**
## ELPIの組込述語

```
typeabbrev id string.

pred coq.locate i:id, o:gref.
pred coq.env.typeof i:gref, o:term.
```
*)

Elpi Query lp:{{
  coq.locate "Nat.add" Gadd,      /* Gadd = const «Nat.add» */
  coq.env.typeof Gadd Ty.
}}.
(**
```
Ty = prod `n` (global (indt «nat»)) 
       c0 \ prod `m` (global (indt «nat»))
       c1 \ global (indt «nat»)
```
*)

Elpi Query lp:{{
  coq.locate "nat" Gnat,          /* Gnat = indt «nat» */
  coq.env.typeof Gnat Ty.         /* Ty = sort (typ «Set») */
}}.

Elpi Query lp:{{
  coq.locate "O" GO,              /* GO = indc «O» */
  coq.env.typeof GO Ty.           /* Ty = global (indt «nat» */
}}.

(**
# Sort

## 定義

```
kind sort       type.
type typ        univ -> sort.
type prop       sort.
type sprop      sort.

type sort       sort -> term.
```
*)

(**
| univ    　| sort          | term                | term       |
|:----------|:-------------|:---------------------|:-----------|
| «set»     | typ «set»     | sort (typ «set»)    | {{Set}}    |
| -         | prop          | sort prop           | {{Prop}}   |
| -         | sprop         | sort sprop          | {{SProp}}  |
| «tut.19»  | typ «tut.19»  | sort (typ «tut.19») | {{Type}}   |
*)

(**
## ELPIの組込述語

```
pred coq.sort.leq o:sort, o:sort.     (* <= *)
pred coq.sort.eq o:sort, o:sort.      (* = *)
pred coq.sort.sup o:sort, o:sort.     (* < *)
```
*)


(**
# Coq項を構成するELPIのコンストラクタ

``fun (x : T) => E`` などの、coq項を構成する構造は、ELPIのコンストラクタとして定義されます。
原則として、coq項からcoq項を組み立てるのですが、CoqのGoalを表示するための表示名としてnameをとるものもあります。
この表示名は、HOASの処理としては、機能しません。

```
type app        list term -> term.
type fun        name -> term -> (term -> term) -> term.
type prod       name -> term -> (term -> term) -> term.
type fix        name -> int -> term -> (term -> term) -> term.
type match      term -> term -> list term -> term.
type let        name -> term -> term -> (term -> term) -> term.
```
*)

(**
# Context

```
prod と同じだが、predとして実行される。
type @pi-decl   name -> term -> (term -> term) -> pred.

let と同じだが、predとして実行される。
type @pi-def    name -> term -> term -> (term -> term) -> pred.
```
*)

Elpi Query lp:{{
  T = {{ fun x : nat => x + 1 }},
  coq.typecheck T _ ok,
  T =  fun N Ty Bo,
                   /* ここの括弧は省略できる */
  @pi-decl N Ty (x\ coq.typecheck (Bo x) _ ok)
}}.

Elpi Query lp:{{
  T = {{ fun x : nat => x + 1 }},
  coq.typecheck T _ ok,
  T =  fun N Ty Bo,
                     /* ここの括弧は省略できる */
  @pi-def N Ty {{1}} (x\ coq.typecheck (Bo x) _ ok)
}}.

(* END *)
