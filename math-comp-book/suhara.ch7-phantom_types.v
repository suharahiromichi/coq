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
(* Set Printing All. *)

(**
# phant の例

こっちのほうが、よく使う。

7. Hierarchies
7.4 Parameters and constructors
*)

(**
phant の定義は、

```Inductive phant (p : Type) := Phant.```

で与えられるが、以下のように書くとわかりやすい。
*)
Inductive phant (p : Type) :=
| Phant : phant p.

(**
値コンストラクタで作った ``Phant p`` の型は、
型コンストラクタで作った ``phant p`` になる。
*)
Check Phant bool : phant bool.

(**
## finset の例
*)

(* ``{set T}`` として、
T に  finType にカノニカルプロジェクションできる型だけを書きたい。
 *)

Definition set_of'' (T : finType) (a : (phant (Finite.sort T))) := seq T.
Arguments set_of'' : clear implicits.
(* Finite.sort はコアーションで省略できる。 *)
Definition set_of (T : finType) (a : phant T) := seq T.
Arguments set_of : clear implicits.

Notation "{ 'set' T }" := (set_of _ (Phant T))
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
Check set_of bool_finType (Phant bool).

(**
カノニカルストラクチャで、bool_finType が見つかるので、引数は省略できる。

``bool <- Finite.sort ( bool_finType )``
 *)
Check set_of _            (Phant bool).

(**
構文糖を適用すると、
 *)
Set Printing All.
Check {set bool}.
(* set_of bool_finType (Phant bool) : Type *)
Unset Printing All.

(**
これは、seq bool とおなじ。
*)
Compute {set bool}.                         (* seq bool *)

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
Arguments finfun_of : clear implicits.

Notation "{ 'ffun' fT }" := (finfun_of _ _ (Phant fT))
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
Check finfun_of bool_finType nat (Phant (bool -> nat)).

(**
カノニカルストラクチャで、bool_finType が見つかるので、引数は省略できる。

``bool <- Finite.sort ( bool_finType )``
 *)
Check @finfun_of _           _   (Phant (bool -> nat)).

(**
構文糖を適用すると、
 *)
Set Printing All.
Check {ffun bool -> nat}.
(* finfun_of bool_finType nat (Phant (bool -> nat)) : predArgType *)
Unset Printing All.


(**
# phantom の例

mcb : 5.11.1 Phantom types

math-comp-book には、以下の例が説明されているが(eqTypeを使う)、
MathCompの定義で使われているのは、上記の phant Phant の方である。
なので、参考として記載しておく。
 *)

(**
phantom の定義は、

```Inductive phantom (T : Type) (p : Type) := Phantom.```

で与えられるが、以下のように書くとわかりやすい。
*)
Inductive phantom (T : Type) (p : Type) :=
| Phantom : phantom T p.
Arguments phantom : clear implicits.

(**
値コンストラクタで作った ``Phantom T p`` の型は、
型コンストラクタで作った ``phantom T p`` になる。
*)
Check Phantom Type bool.

(**
``{set T}`` として、
T に finType にカノニカルプロジェクションできる型だけを書きたい。
 *)

Definition set_of' (T : finType) (a : phantom Type (Finite.sort T)) := seq T.
Arguments set_of' : clear implicits.

Notation "{ 'set' T }" := (set_of' _ (Phantom _ T))
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
Check set_of' bool_finType (Phantom Type bool).

(**
カノニカルストラクチャで、bool_finType が見つかるので、引数は省略できる。

``bool <- Finite.sort ( bool_finType )``
 *)
Check set_of' _            (Phantom _    bool).

(**
構文糖を適用すると、
 *)
Set Printing All.
Check {set bool}.
(* set_of' bool_finType (Phantom Type bool) : Type *)
Unset Printing All.

(**
これは、seq bool とおなじ。
*)
Compute {set bool}.                         (* seq bool *)

(**
一方、 nat_finType が存在しないので、nat ではエラーになる。
 *)
Fail Check {set nat}.

(* END *)
