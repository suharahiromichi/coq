From elpi Require Import elpi.

Elpi Command tutorial_HOAS.

(**
# Coq の定義

```coq
Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Definition Nat.add := ......

Notation plus := Nat.add.
```
 *)
Definition x : nat := 2.

(**
# ELPIの組込関数

後で説明しますが、ELPIには次の型の関数が定義されています。

```
type const      constant -> gref.
type indt       inductive -> gref.
type indc       constructor -> gref.

type global     gref -> term.
type app        list term -> term.
type fun        name -> term -> (term -> term) -> term.
type fix        name -> int -> term -> (term -> term) -> term.
type match      term -> term -> list term -> term.

type sort       universe -> term.
type prop       universe.
type typ        univ -> universe.
```

*)

(**
# Gallina の HOAS

## coq.locate

Coqの識別子（文字列で与える）に対して、ELPIのgref型の項を返す。
*)
Elpi Query lp:{{
      coq.locate "nat" GRnat,               /* indt «nat» */
      coq.locate "O" GRo,                   /* indc «O» */
      coq.locate "S" GRs,                   /* indc «S» */
      coq.locate "Nat.add" GRplus,          /* const «Nat.add» */
      coq.locate "plus" GRplus,             /* const «Nat.add» */
      coq.locate "x" GR                     /* const «x» */
  }}.

(**
coq.locate の結果：
indt、indc、const は gref型を返す関数である。
``«x»`` は ``<<x>>`` ではなく、ELPIのコードには書けないようである。

| Coq       | ELPI                  | 意味             |
|-----------|-----------------------|------------------|
| nat       | indt «nat»            | Type             |
| O         | indc «O»              | Constructor      |
| S         | indc «S»              | Constructor      |
| Nat.add   | const «Nat.add»       | 定数 †           |
| x         | const «x»             | 定数 †           |
|-----------|-----------------------|------------------|

† 定数は、Definitionで定義されたもの。Notationは展開される。
 *)

(**
## coq.env.typeof

項に対して型を返す。
``x : nat`` であるとき、``const «x»`` の型として ``indt  «nat»`` を返す。
*)

Check x : nat.

Elpi Query lp:{{
      coq.locate "x" GR,                    /* const «x» */
      coq.env.typeof GR (global Ty)         /* indt «nat» */
  }}.

(**
## coq.env.const

定数に対して、その内容と、型を返す。
 *)

Elpi Query lp:{{
      coq.locate "x" (const C),              /* «x» */
      coq.env.const C (some Bo)
      /* app [global (indc «S»), app [global (indc «S»), global (indc «O»)]] */
                    (global Ty)             /* indt «nat» */
  }}.

(**
## ELPIの fun、fix と match 関数
 *)
Definition f := fun x : nat => x.

Elpi Query lp:{{
      coq.locate "f" (const C),             /* «f» */
      coq.env.const C (some Bo) _           /* fun `x` (global (indt «nat»)) c0 \ c0 */
  }}.

Elpi Query lp:{{
      coq.locate "plus" (const C),          /* «Nat.add» */
      coq.env.const C (some Bo) _           /* (略) */
  }}.

Definition m (h : 0 = 1 ) P : P 0 -> P 1 :=
  match h as e in eq _ x return P 0 -> P x
  with eq_refl => fun (p : P 0) => p end.

Elpi Query lp:{{
      coq.locate "m" (const C),
      coq.env.const C (some (fun _ _ h\ fun _ _ p\ match _ (RT h p) _)) _
  }}.


Elpi Query lp:{{
      coq.univ.sup U U1,
      coq.say U "<" U1,
      /* This constraint can't be allowed in the store! */
      not(coq.univ.leq U1 U)
  }}.

(**
## ELPI の sort 関数

略
 *)

(**
# Gallina 項の参照

``lp:{{ ... }}`` の中で ``{{ ... }}`` で、coq.locate述語が埋め込めると考えればよい。
さらにその中に、``lp:{{ ... }}`` で LPI が書ける。
*)

Elpi Query lp:{{
      coq.locate "x" X1,                    /* const «x» */
      {{x}} = X2                            /* global (const «x») */
  }}.

(**
## 例 
 *)
Elpi Query lp:{{
      {{:coq 1 + 2 }} = R1,
      {{ 1 + 2 }} = R1,
      
      {{ 1 + lp:{{ app[global S, {{ 0 }} ]  }}   }} = R2,
      
      (fun `x` {{nat}} x\ {{ fun x : nat => x + lp:{{ x }} }}) = R3,
      (fun `x` {{nat}} x\ {{ fun x : nat => x + lp:x }}) = R3,

      X = (x\y\ {{ lp:y + lp:x }}),
      {{ fun a b : nat => lp:(X a b) }} = R4
  }}.

Register Coq.Init.Datatypes.nat as my.N.
Register Coq.Init.Logic.eq as my.eq.

Elpi Query lp:{{
      {{ fun a b : lib:my.N => lib:@my.eq lib:my.N a b }} = R1,

      {{:gref  nat  }} = R2,
      {{:gref  lib:my.N  }} = R2,
      {{ nat }} = global R2                  /* globalが付く。 */
  }}.


Elpi Query lp:{{
      T = (fun `ax` {{nat}} a\ {{ fun b : nat => lp:a = b }}),
      
      coq.say "before:" T,
      coq.typecheck T _ ok,
      coq.say "after:" T
  }}.

(* END *)
