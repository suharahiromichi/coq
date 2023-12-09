(**
ssralg.v サンプル
*)
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
From mathcomp Require Import ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.
Open Scope ring_scope.

(**
# 型の階層図
*)

(**
```
eqType
|
choiceType
|
nmodType
|\
| +-------------------+
|                      \
zmodType                semiRingType
|                      /|
| +-------------------+ |
|/                      |
RingType                comSemiRingTYpe
|                       |
|                       |
|                       |
unitRingType            comRingType
|                      /
| +-------------------+
|/
comUnitRingType
|
|
idomainType ~~~ (int)
|
|
fieldType
```

- unitRingType は、逆元が存在する型。

- idomainType は整域公理「零因子が0しかない」``m * n = 0 -> (m == 0) || (n == 0)`` が成り立つ型。

- fieldType は、体の公理「0でなければ逆元を持つ」``x != 0 -> x \is a unit`` が成り立つ型。
*)

(**
# 覚えておくべき
 *)
Check @zero : forall s : nmodType, s.                 (* 0 *)
Check @add  : forall s : nmodType, s -> s -> s.       (* x + y *)
Check @opp  : forall s : zmodType, s -> s.            (* - x *)
Check @mul  : forall s : semiRingType, s -> s -> s.   (* x * y *)
Check one   : forall s : semiRingType, s.             (* 1 *)
Check @inv  : forall s : unitRingType, s -> s.        (* x ^-1 *)
Check natmul : forall V : nmodType, V -> nat -> V.    (* x *+ n *)
Check exp   : forall R : semiRingType, R -> nat -> R. (* x ^+ n *)

Locate "x - y".               (* := (add x (opp y)) : ring_scope *)
Locate "x *- n".              (* := (opp (natmul x n)) : ring_scope *)
Check (fun x y => x - y)  : (_ : zmodType) -> (_ : zmodType) -> (_ : zmodType).
Check (fun x n => x *- n) : (_ : zmodType) -> nat -> (_ : zmodType).

Locate "n %:R".               (* := (natmul (one _) n) : ring_scope *)
Check (fun n => n%:R)     : nat -> (_ : semiRingType).

Locate "x / y".                  (* := (mul x (inv y)) : ring_scope *)
Locate "x ^- n".                 (* := (inv (exp x n)) : ring_scope *)
Check (fun x y => x / y)  : (_ : unitRingType) -> (_ : unitRingType) -> (_ : unitRingType).
Check (fun x n => x ^- n) : (_ : unitRingType) -> nat -> (_ : unitRingType).

Check @addrA : forall s : nmodType, associative +%R.
Check @addrC : forall s : nmodType, commutative +%R.
Check @mulrA : forall s : semiRingType, associative *%R.
Check @mulrC : forall s : comSemiRingType, commutative *%R.

(**
# 型ごとの関数と補題
*)
(**
## nmodType アーベル・モノイド
 *)
Check @zero : forall s : nmodType, s.                  (* 0 *)
Check @add  : forall s : nmodType, s -> s -> s.        (* x + y *)
Fail Check @opp  : forall s : nmodType, s -> s.        (* - x *)
Fail Check @mul  : forall s : nmodType, s -> s -> s.   (* x * y *)
Fail Check one   : forall s : nmodType, s.             (* 1 *)
Fail Check @inv  : forall s : nmodType, s -> s.        (* x ^-1 *)
Check natmul : forall V : nmodType, V -> nat -> V.     (* x *+ n *)
Fail Check exp   : forall R : nmodType, R -> nat -> R. (* x ^+ n *)

Search add    nmodType.
Search natmul nmodType.                     (* _ *+ _ *)

Check mulrnDl : forall (V : nmodType) (n : nat), {morph (@natmul V)^~ n : x y / x + y}.
Check mulrnDl : forall (V : nmodType) (n : nat) (x y : V), (x + y) *+ n = x *+ n + y *+ n.

Check raddfMn : forall (U V : nmodType) (f : {additive U -> V}) (n : nat), {morph f : x / x *+ n >-> x *+ n}.
Check raddfMn : forall (U V : nmodType) (f : {additive U -> V}) (n : nat) (x : U), f (x *+ n) = (f x) *+ n.

(**
## zmodType アーベル群
 *)
Check @zero : forall s : zmodType, s.                  (* 0 *)
Check @add  : forall s : zmodType, s -> s -> s.        (* x + y *)
Check @opp  : forall s : zmodType, s -> s.             (* - x *)
Fail Check @mul  : forall s : zmodType, s -> s -> s.   (* x * y *)
Fail Check one   : forall s : zmodType, s.             (* 1 *)
Fail Check @inv  : forall s : zmodType, s -> s.        (* x ^-1 *)
Check natmul : forall V : zmodType, V -> nat -> V.     (* x *+ n *)
Fail Check exp   : forall R : zmodType, R -> nat -> R. (* x ^+ n *)

Search natmul   zmodType.                   (* _ *+ _ *)
Search (_ *- _) zmodType.
Search add      zmodType.
Search (_ - _)  zmodType.

(**
## semiRingType
 *)
Check @zero : forall s : semiRingType, s.              (* 0 *)
Check @add  : forall s : semiRingType, s -> s -> s.    (* x + y *)
Fail Check @opp  : forall s : semiRingType, s -> s.    (* - x *)
Check @mul  : forall s : semiRingType, s -> s -> s.    (* x * y *)
Check one   : forall s : semiRingType, s.              (* 1 *)
Fail Check @inv  : forall s : semiRingType, s -> s.    (* x ^-1 *)
Check natmul : forall V : semiRingType, V -> nat -> V. (* x *+ n *)
Check exp   : forall R : semiRingType, R -> nat -> R.  (* x ^+ n *)

Search natmul   semiRingType.               (* _ *+ _ *)
Search (_ *- _) semiRingType.
Search add      semiRingType.               (* _ + _ *)
Search mul      semiRingType.               (* _ * _ *)

Check commr_nat: forall [R : semiRingType] (x : R) (n : nat), comm x n%:R.
Check commr_nat: forall [R : semiRingType] (x : R) (n : nat), x * n%:R = n%:R * x.

(**
## ringType
 *)
Check @zero : forall s : ringType, s.              (* 0 *)
Check @add  : forall s : ringType, s -> s -> s.    (* x + y *)
Check @opp  : forall s : ringType, s -> s.         (* - x *)
Check @mul  : forall s : ringType, s -> s -> s.    (* x * y *)
Check one   : forall s : ringType, s.              (* 1 *)
Fail Check @inv  : forall s : ringType, s -> s.    (* x ^-1 *)
Check natmul : forall V : ringType, V -> nat -> V. (* x *+ n *)
Check exp   : forall R : ringType, R -> nat -> R.  (* x ^+ n *)

Search natmul   ringType.                   (* _ *+ _ *)
Search (_ *- _) ringType.
Search add      ringType.                   (* _ + _ *)
Search mul      ringType.                   (* _ * _ *)

(**
## comSemiRingType
 *)
Check @zero : forall s : comSemiRingType, s.              (* 0 *)
Check @add  : forall s : comSemiRingType, s -> s -> s.    (* x + y *)
Fail Check @opp  : forall s : comSemiRingType, s -> s.    (* - x *)
Check @mul  : forall s : comSemiRingType, s -> s -> s.    (* x * y *)
Check one   : forall s : comSemiRingType, s.              (* 1 *)
Fail Check @inv  : forall s : comSemiRingType, s -> s.    (* x ^-1 *)
Check natmul : forall V : comSemiRingType, V -> nat -> V. (* x *+ n *)
Check exp   : forall R : comSemiRingType, R -> nat -> R.  (* x ^+ n *)

Search natmul   comSemiRingType.            (* _ *+ _ *)
Search (_ *- _) comSemiRingType.
Search add      comSemiRingType.            (* _ + _ *)
Search mul      comSemiRingType.            (* _ * _ *)

(**
## comRingType
 *)
Check @zero : forall s : comRingType, s.              (* 0 *)
Check @add  : forall s : comRingType, s -> s -> s.    (* x + y *)
Check @opp  : forall s : comRingType, s -> s.         (* - x *)
Check @mul  : forall s : comRingType, s -> s -> s.    (* x * y *)
Check one   : forall s : comRingType, s.              (* 1 *)
Fail Check @inv  : forall s : comRingType, s -> s.    (* x ^-1 *)
Check natmul : forall V : comRingType, V -> nat -> V. (* x *+ n *)
Check exp   : forall R : comRingType, R -> nat -> R.  (* x ^+ n *)

Search natmul   comRingType.                (* _ *+ _ *)
Search (_ *- _) comRingType.
Search add      comRingType.                (* _ + _ *)
Search mul      comRingType.                (* _ * _ *)

(**
## unitRingType
 *)
Check @zero : forall s : unitRingType, s.              (* 0 *)
Check @add  : forall s : unitRingType, s -> s -> s.    (* x + y *)
Check @opp  : forall s : unitRingType, s -> s.         (* - x *)
Check @mul  : forall s : unitRingType, s -> s -> s.    (* x * y *)
Check one   : forall s : unitRingType, s.              (* 1 *)
Check @inv  : forall s : unitRingType, s -> s.         (* x ^-1 *)
Check natmul : forall V : unitRingType, V -> nat -> V. (* x *+ n *)
Check exp   : forall R : unitRingType, R -> nat -> R.  (* x ^+ n *)

Search natmul   unitRingType.               (* _ *+ _ *)
Search (_ *- _) unitRingType.
Search exp      unitRingType.               (* _ ^- _ *)
Search add      unitRingType.
Search mul      unitRingType.
Search (_ / _)  unitRingType.
Search inv      unitRingType.

(**
## comUnitRingType
 *)
Check @zero : forall s : comUnitRingType, s.              (* 0 *)
Check @add  : forall s : comUnitRingType, s -> s -> s.    (* x + y *)
Check @opp  : forall s : comUnitRingType, s -> s.         (* - x *)
Check @mul  : forall s : comUnitRingType, s -> s -> s.    (* x * y *)
Check one   : forall s : comUnitRingType, s.              (* 1 *)
Check @inv  : forall s : comUnitRingType, s -> s.         (* x ^-1 *)
Check natmul : forall V : comUnitRingType, V -> nat -> V. (* x *+ n *)
Check exp   : forall R : comUnitRingType, R -> nat -> R.  (* x ^+ n *)

Search natmul   comUnitRingType.            (* _ *+ _ *)
Search (_ *- _) comUnitRingType.
Search exp      comUnitRingType.            (* _ ^- _ *)
Search add      comUnitRingType.
Search mul      comUnitRingType.
Search (_ / _)  comUnitRingType.
Search inv      comUnitRingType.

(**
## idomainType
 *)
Print integral_domain_axiom.
(*  = fun R : ringType => forall x y : R, x * y = 0 -> (x == 0) || (y == 0) *)

Check @zero : forall s : idomainType, s.              (* 0 *)
Check @add  : forall s : idomainType, s -> s -> s.    (* x + y *)
Check @opp  : forall s : idomainType, s -> s.         (* - x *)
Check @mul  : forall s : idomainType, s -> s -> s.    (* x * y *)
Check one   : forall s : idomainType, s.              (* 1 *)
Check @inv  : forall s : idomainType, s -> s.         (* x ^-1 *)
Check natmul : forall V : idomainType, V -> nat -> V. (* x *+ n *)
Check exp   : forall R : idomainType, R -> nat -> R.  (* x ^+ n *)

Search natmul   idomainType.            (* _ *+ _ *)
Search (_ *- _) idomainType.
Search exp      idomainType.            (* _ ^- _ *)
Search add      idomainType.
Search mul      idomainType.
Search (_ / _)  idomainType.
Search inv      idomainType.

(**
## fieldType
 *)
Print field_axiom.
(* = fun R : unitRingType => forall x : R, x != 0 -> x \is a unit *)
(* x \is a unit == x \in unit ~~ GRing.unit x ~~ has an inverse *)
Check unitrV : forall (R : unitRingType) (x : R), (x^-1 \is a unit) = (x \is a unit).
Check unitrE : forall (R : unitRingType) (x : R), (x \is a unit) = (x / x == 1).

Check @zero : forall s : fieldType, s.              (* 0 *)
Check @add  : forall s : fieldType, s -> s -> s.    (* x + y *)
Check @opp  : forall s : fieldType, s -> s.         (* - x *)
Check @mul  : forall s : fieldType, s -> s -> s.    (* x * y *)
Check one   : forall s : fieldType, s.              (* 1 *)
Check @inv  : forall s : fieldType, s -> s.         (* x ^-1 *)
Check natmul : forall V : fieldType, V -> nat -> V. (* x *+ n *)
Check exp   : forall R : fieldType, R -> nat -> R.  (* x ^+ n *)

Search natmul   fieldType.            (* _ *+ _ *)
Search (_ *- _) fieldType.
Search exp      fieldType.            (* _ ^- _ *)
Search add      fieldType.
Search mul      fieldType.
Search (_ / _)  fieldType.
Search inv      fieldType.

(* END *)
