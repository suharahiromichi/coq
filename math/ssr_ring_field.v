(**
MathComp の環・体
========================

@suharahiromichi

2020/07/17
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import ssromega.                    (* ssromega タクティク *)
Require Import Recdef.                      (* Function コマンド *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* (x + y)%Rを省略時解釈とする。 *)

(*
# 加群 Zmodule
 *)
Section ZModule.
  Variable V : zmodType.

  Check @addrC V : forall x y : V, (x + y) = (y + x).
  Check @addrA V : forall x y z : V, (x + (y + z)) = (x + y + z).
End ZModule.

(**
# 環 ring
*)
Section Ring.
  Variable R : ringType.
  
  Check @mulrA R : forall x y z : R, (x * (y * z)) = (x * y * z).
End Ring.

(**
# 1をもつ環
*)
Section UnitRing.
  Variable R : unitRingType.
  
  Check @divrr R : forall x : R, x \is a GRing.unit -> (x / x) = 1.
End UnitRing.

(**
# 可換環 commutative ring
*)
Section ComRing.
  Variable R : comRingType.
End ComRing.

(**
# 1をもつ可換環
*)
Section ComUnitRing.
  Variable R : comUnitRingType.
  
  Check @unitrM R
    : forall x y : R,
      (x * y) \is a GRing.unit = (x \is a GRing.unit) && (y \is a GRing.unit).
End ComUnitRing.

(**
# 整域 integral domain
*)
Section IntDomain.
  Variable R : idomainType.

  Check @mulf_eq0 R
    : forall x y : R, ((x * y) == 0) = (x == 0) || (y == 0).
End IntDomain.

(**
# 体 field
*)
Section Field.
  Variable F : fieldType.

  Check @divff F
    : forall x : F, x != 0 -> (x / x) = 1.
End Field.

(**
# おまけ

冒頭で ring_scope を設定しています。
これは + の省略時解釈を GRing.add とすることです。
 *)
Locate "_ + _".
(*
"m + n" := Nat.add m n : coq_nat_scope
"A + B" := addsmx A B : matrix_set_scope
"m + n" := addn_rec m n : nat_rec_scope
"m + n" := addn m n : nat_scope
"x + y" := addq x y : rat_scope (default interpretation)
"x + y" := GRing.add x y : ring_scope
"x + y" := GRing.Add x y : term_scope
"x + y" := sum x y : type_scope
"U + V" := addv U V : vspace_scope
*)

(* 以下において、Checkの出力の %X が消えることに注意してください。 *)
Open Scope coq_nat_scope.
Check (1 + 1)%coq_nat : nat.

Open Scope nat_scope.
Check (1 + 1)%N : nat.

Open Scope ring_scope.
Variable R : ringType.
Check (1 + 1)%R : R.

Open Scope term_scope.
Check (1 + 1)%T : GRing.term R.

Open Scope type_scope.
Check (nat + nat)%type : Set.

Open Scope rat_scope.
Check (1 + 1)%Q.

(* END *)
