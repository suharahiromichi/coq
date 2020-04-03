(**
MathComp のおける Phantom Type の使用例
============

@suharahiromichi

2020/04/03
*)

(**
# 概要

MathComp のおける Phantom Type の使用例を調べてみた。

- {set T}
- {perm T}
- {ffun aT -> rT}
- {poly R}

 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing All.

(**
# phantom の例

mcb : 5.11.1 Phantom types
 *)

Inductive phantom (T : Type) (p : Type) := Phantom.
Arguments phantom : clear implicits.

(**
``{set T}`` として、
T に finType にカノニカルプロジェクションできる型だけを書きたい。
 *)

Definition set_of' (T : finType) (a : phantom Type (Finite.sort T)) := seq T.

Notation "{ 'set' T }" := (@set_of' _ (Phantom _ T))
                            (at level 0, format "{ 'set' T }") : type_scope.

(**
set_of' の引数を調べる：
 *)

(**
T について、bool_finType は finType のインスタンスである。
 *)
Check bool_finType : finType.

(**
a について、

``T = bool_finType`` の場合、 ``Finite.sort bool_finType`` は bool である。

``a = Phantom Type bool`` は、 ``phantom Type bool`` の型を持つ。
 *)
Compute Equality.sort bool_finType.           (* = bool *)
Check Phantom Type bool : phantom Type (Finite.sort bool_finType).
Check Phantom Type bool : phantom Type bool.

(**
以上より、
 *)
Check @set_of' bool_finType (Phantom Type bool).

(**
カノニカルストラクチャで、bool_finType が見つかるので、引数は省略できる。

``bool <- Finite.sort ( bool_finType )``
 *)
Check @set_of' _            (Phantom _    bool).

(**
構文糖を適用すると、
 *)
Check {set bool}.

(**
一方、 nat_finType が存在しないので、nat ではエラーになる。
 *)
Fail Check {set nat}.

(**
# phant の例

こっちのほうが、よく使う。

7. Hierarchies
7.4 Parameters and constructors
*)

Inductive phant (p : Type) := Phant.

(**
## finset の例
*)

(* ``{set T}`` として、
T に  finType にカノニカルプロジェクションできる型だけを書きたい。
 *)

Definition set_of (T : finType) (a : phant T) := seq T.

Notation "{ 'set' T }" := (@set_of _ (Phant T))
                            (at level 0, format "{ 'set' T }") : type_scope.

(**
set_of の引数を調べる：
 *)

(**
T について、bool_finType は finType のインスタンスである。
 *)
Check bool_finType : finType.

(**
a について、

``T = bool_finType`` の場合、

a の型 ``phant bool_finType`` は、
コアーションにより ``phant bool`` になるので、``a = Phant bool``
 *)
Check Phant bool : phant bool_finType.
Check Phant bool : phant (Finite.sort bool_finType).
Check Phant bool : phant bool.

(**
以上より、
 *)
Check @set_of bool_finType (Phant bool).

(**
カノニカルストラクチャで、bool_finType が見つかるので、引数は省略できる。

``bool <- Finite.sort ( bool_finType )``
 *)
Check @set_of _            (Phant bool).

(**
構文糖を適用すると、
 *)
Check {set bool}.

(**
一方、nat_finType が存在しないので、nat ではエラーになる。
 *)
Fail Check {set nat}.


(**
## finfun の例
 *)

(*
Section Def.
Variables (aT : finType) (rT : Type).
Inductive finfun_type : predArgType := Finfun of #|aT|.-tuple rT.
Definition finfun_of of phant (aT -> rT) := finfun_type.
End Def.
*)

(**
``{ffin aT -> rT}`` として、
aT が finType にカノニカルプロジェクションできること。
 *)

Inductive finfun_type (aT : finType) (rT : Type) : predArgType :=
  Finfun of #|aT|.-tuple rT.
Definition finfun_of (aT : finType) (rT : Type) (a : phant (aT -> rT)) :=
  finfun_type aT rT.

Notation "{ 'ffun' fT }" := (@finfun_of _ _ (Phant fT))
  (at level 0, format "{ 'ffun'  '[hv' fT ']' }") : type_scope.

(**
finfun_of の引数を調べる：

aT について、bool_finType は finType のインスタンスである。
 *)
Check bool_finType : finType.

(**
rT について、
 *)
Check nat : Type.

(**
``aT = bool_finType`` ``rT = nat`` のとき、

a の型 ``phant (bool_finType -> nat)`` は、
コアーションにより ``phant (bool -> nat)`` になるので、``a = Phant (bool -> nat)``
 *)
Check Phant (bool -> nat) : phant (bool_finType -> nat).
Check Phant (bool -> nat) : phant ((Finite.sort bool_finType) -> nat).
Check Phant (bool -> nat) : phant (bool -> nat).

(**
以上より、
 *)
Check @finfun_of bool_finType nat (Phant (bool -> nat)).

(**
カノニカルストラクチャで、bool_finType が見つかるので、引数は省略できる。

``bool <- Finite.sort ( bool_finType )``
 *)
Check @finfun_of _            _   (Phant (bool -> nat)).

(**
構文糖を適用すると、
 *)
Check {ffun bool -> nat}.

(* END *)
