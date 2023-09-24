(**
ssrnum.v サンプル
*)
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
From mathcomp Require Import ssralg ssrnum.

(**
# 型の階層図
*)

(**
```
zmodType
|\
| +-------------------+
|                      \
porderZmodType          normedZmodType
|                      /
| +-------------------+
|/
numDomainType
|
|
realDomainType
```
*)


Import Num.Theory.
Import Num.Def.

Local Open Scope order_scope.
Local Open Scope ring_scope.

Locate "'Re".

