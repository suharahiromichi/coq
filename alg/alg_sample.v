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

- unit...Type は、unitは``1``のことで、逆元が存在する型。

- idomainType は整域公理 ``m * n = 0 -> (m == 0) || (n == 0)`` が成り立つ型。
*)

(**
# 覚えておくべき
 *)
Check zero : (_ : nmodType).                                     (* 0 *)
Check add  : (_ : nmodType) -> (_ : nmodType) -> (_ : nmodType). (* +%R, + *)
Check opp  : (_ : zmodType) -> (_ : zmodType).                   (* -%R, - *)
Check mul  : (_ : semiRingType) -> (_ : semiRingType) -> (_ : semiRingType). (* *%R, * *)
Check one  : forall (s : semiRingType), s.             (* 1 *)
Check inv  : (_ : unitRingType) -> (_ : unitRingType). (* ^-1 *)

Notation "x *+ n" := (natmul x n) : ring_scope. (* nmodType *)
Notation "- x"    := (opp x) : ring_scope.      (* zmodType *)
Notation "x ^+ n" := (exp x n) : ring_scope.    (* semiRingType *)
Notation "x ^-1"  := (inv x).                   (* unitRingType *)

Notation "x - y"  := (x + - y) : ring_scope.     (* zmodType *)
Notation "x *- n" := (- (x *+ n)) : ring_scope.  (* zmodType *)
Notation "n %:R"  := (1 *+ n) : ring_scope.      (* semiRingType *)
Notation "x / y"  := (x * y^-1).                 (* unitRingType *)
Notation "x ^- n" := ((x ^+ n)^-1).              (* unitRingType *)

Check @addrA : forall s : nmodType, associative +%R.
Check @addrC : forall s : nmodType, commutative +%R.
Check @mulrA : forall s : semiRingType, associative *%R.
Check @mulrC : forall s : comSemiRingType, commutative *%R.

(**
# 型ごとの関数と補題
*)

(* nmodType *)
Check zero : (_ : nmodType).
Check add  : (_ : nmodType) -> (_ : nmodType) -> (_ : nmodType).
Search add    nmodType.
Search natmul nmodType.                     (* _ *+ _ *)

Check mulrnDl : forall (V : nmodType) (n : nat), {morph (@natmul V)^~ n : x y / x + y}.
Check mulrnDl : forall (V : nmodType) (n : nat) (x y : V), (x + y) *+ n = x *+ n + y *+ n.

Check raddfMn : forall (U V : nmodType) (f : {additive U -> V}) (n : nat), {morph f : x / x *+ n >-> x *+ n}.
Check raddfMn : forall (U V : nmodType) (f : {additive U -> V}) (n : nat) (x : U), f (x *+ n) = (f x) *+ n.

(* zmodType *)
Check zero : (_ : zmodType).
Check add  : (_ : zmodType) -> (_ : zmodType) -> (_ : zmodType).
Check opp  : (_ : zmodType) -> (_ : zmodType).
Local Notation "x - y" := (x + - y) : ring_scope.
Local Notation "x *- n" := (- (x *+ n)) : ring_scope.
Search natmul   zmodType.                   (* _ *+ _ *)
Search (_ *- _) zmodType.
Search add      zmodType.
Search (_ - _)  zmodType.

(* semiRingType *)
Check zero : (_ : semiRingType).
Check add  : (_ : semiRingType) -> (_ : semiRingType) -> (_ : semiRingType).
Check opp  : (_ : semiRingType) -> (_ : semiRingType).
Check mul  : (_ : semiRingType) -> (_ : semiRingType) -> (_ : semiRingType).
Check one  : forall (s :  semiRingType), s.
Local Notation "n %:R" := (1 *+ n) : ring_scope.
Search natmul   semiRingType.               (* _ *+ _ *)
Search (_ *- _) semiRingType.
Search add      semiRingType.               (* _ + _ *)
Search mul      semiRingType.               (* _ * _ *)

Check commr_nat: forall [R : semiRingType] (x : R) (n : nat), comm x n%:R.
Check commr_nat: forall [R : semiRingType] (x : R) (n : nat), x * n%:R = n%:R * x.

(* ringType *)
Check zero : (_ : ringType).
Check add  : (_ : ringType) -> (_ : ringType) -> (_ : ringType).
Check opp  : (_ : ringType) -> (_ : ringType).
Check mul  : (_ : ringType) -> (_ : ringType) -> (_ : ringType).
Check one  : forall (s :  ringType), s.
Search natmul   ringType.                   (* _ *+ _ *)
Search (_ *- _) ringType.
Search add      ringType.                   (* _ + _ *)
Search mul      ringType.                   (* _ * _ *)

(* comSemiRingType *)
Check zero : (_ : comSemiRingType).
Check add  : (_ : comSemiRingType) -> (_ : comSemiRingType) -> (_ : comSemiRingType).
Check opp  : (_ : comSemiRingType) -> (_ : comSemiRingType).
Check mul  : (_ : comSemiRingType) -> (_ : comSemiRingType) -> (_ : comSemiRingType).
Check one  : forall (s :  comSemiRingType), s.
Search natmul   comSemiRingType.            (* _ *+ _ *)
Search (_ *- _) comSemiRingType.
Search add      comSemiRingType.            (* _ + _ *)
Search mul      comSemiRingType.            (* _ * _ *)

(* comRingType *)
Check zero : (_ : comRingType).
Check add  : (_ : comRingType) -> (_ : comRingType) -> (_ : comRingType).
Check opp  : (_ : comRingType) -> (_ : comRingType).
Check mul  : (_ : comRingType) -> (_ : comRingType) -> (_ : comRingType).
Check one  : forall (s :  comRingType), s.
Search natmul   comRingType.                (* _ *+ _ *)
Search (_ *- _) comRingType.
Search add      comRingType.                (* _ + _ *)
Search mul      comRingType.                (* _ * _ *)

(* unitRingType *)
Check zero : (_ : unitRingType).
Check add  : (_ : unitRingType) -> (_ : unitRingType) -> (_ : unitRingType).
Check opp  : (_ : unitRingType) -> (_ : unitRingType).
Check mul  : (_ : unitRingType) -> (_ : unitRingType) -> (_ : unitRingType).
Check one  : forall (s :  unitRingType), s.
Check inv  : (_ : unitRingType) -> (_ : unitRingType).
Local Notation "x / y" := (x * y^-1).
Local Notation "x ^- n" := ((x ^+ n)^-1).
Search natmul   unitRingType.               (* _ *+ _ *)
Search (_ *- _) unitRingType.
Search exp      unitRingType.               (* _ ^- _ *)
Search add      unitRingType.
Search mul      unitRingType.
Search (_ / _)  unitRingType.
Search inv      unitRingType.

(* comUnitRingType *)
Check zero : (_ : comUnitRingType).
Check add  : (_ : comUnitRingType) -> (_ : comUnitRingType) -> (_ : comUnitRingType).
Check opp  : (_ : comUnitRingType) -> (_ : comUnitRingType).
Check mul  : (_ : comUnitRingType) -> (_ : comUnitRingType) -> (_ : comUnitRingType).
Check one  : forall (s :  comUnitRingType), s.
Check inv  : (_ : comUnitRingType) -> (_ : comUnitRingType).
Search natmul   comUnitRingType.            (* _ *+ _ *)
Search (_ *- _) comUnitRingType.
Search exp      comUnitRingType.            (* _ ^- _ *)
Search add      comUnitRingType.
Search mul      comUnitRingType.
Search (_ / _)  comUnitRingType.
Search inv      comUnitRingType.

(* idomainType *)
Check zero : (_ : idomainType).
Check add  : (_ : idomainType) -> (_ : idomainType) -> (_ : idomainType).
Check opp  : (_ : idomainType) -> (_ : idomainType).
Check mul  : (_ : idomainType) -> (_ : idomainType) -> (_ : idomainType).
Check one  : forall (s :  idomainType), s.
Check inv  : (_ : idomainType) -> (_ : idomainType).
Search natmul   idomainType.            (* _ *+ _ *)
Search (_ *- _) idomainType.
Search exp      idomainType.            (* _ ^- _ *)
Search add      idomainType.
Search mul      idomainType.
Search (_ / _)  idomainType.
Search inv      idomainType.

(* fieldType *)
Check zero : (_ : fieldType).
Check add  : (_ : fieldType) -> (_ : fieldType) -> (_ : fieldType).
Check opp  : (_ : fieldType) -> (_ : fieldType).
Check mul  : (_ : fieldType) -> (_ : fieldType) -> (_ : fieldType).
Check one  : forall (s :  fieldType), s.
Check inv  : (_ : fieldType) -> (_ : fieldType).
Search natmul   fieldType.            (* _ *+ _ *)
Search (_ *- _) fieldType.
Search exp      fieldType.            (* _ ^- _ *)
Search add      fieldType.
Search mul      fieldType.
Search (_ / _)  fieldType.
Search inv      fieldType.

(* END *)
