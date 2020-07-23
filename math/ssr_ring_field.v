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

  (* opposite (単項マイナス演算子) は、 *)
  Check @opprD V : {morph -%R : x y / x + y}.

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

  Check @mulf_eq0 R : forall x y : R,
      ((x * y) == 0) = (x == 0) || (y == 0).
End IntDomain.

(**
# number domain (number field)

order (順番) と norm (絶対値) のある整域（または体）(例：ガウス整数)
*)
Section NumDomain.
  Variable R : numDomainType.

  Check @ler_norm_add R : forall x y : R,
      `|x + y| <= `|x| + `|y|.
End NumDomain.

(**
# 体 field
*)
Section Field.
  Variable F : fieldType.
  
  Check @divff F : forall x : F,
      x != 0 -> (x / x) = 1.
End Field.

(**
# real field

要素に正負のある number field （例：実数）
*)
Section RealField.
  Variables rF : realFieldType.
  
  Check @lerif_mean_square rF : forall x y : rF,
      x * y <= (x ^+ 2 + y ^+ 2) / 2%:R ?= iff (x == y).
  
  (* 左辺の=が成り立つことと、x = y であることが同値  *)
End RealField.

(**
# 閉体 closed field

多項式の根がある体。
*)
Section ClosedField.
  (* 補足すること。 *)
End ClosedField.


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
"m + n" := addn m n : nat_scope ← 通常、これが省略時解釈。
"x + y" := addq x y : rat_scope ← ここでは、これが省略時解釈。
"x + y" := GRing.add x y : ring_scope
"x + y" := GRing.Add x y : term_scope
"x + y" := sum x y : type_scope
"U + V" := addv U V : vspace_scope
*)

(* 以下において、Checkの出力の %X が消えることに注意してください。 *)
(* ProofGeneral では、読み直さないといけない場合があります。 *)

(* ssrnat.v:Delimit Scope coq_nat_scope with coq_nat. *)
Open Scope coq_nat_scope.
Check (1 + 1)%coq_nat : nat.

(* ssrnat.v:Delimit Scope nat_scope with N. *)
Open Scope nat_scope.
Check (1 + 1)%N : nat.

(* ssralg.v:Delimit Scope ring_scope with R. *)
Open Scope ring_scope.
Variable R : ringType.
Check (1 + 1)%R : R.

(* ssralg.v:Delimit Scope term_scope with T. *)
Open Scope term_scope.
Check (1 + 1)%T : GRing.term R.

Open Scope type_scope.
Check (nat + nat)%type : Set.

(* rat.v:Delimit Scope rat_scope with Q. *)
Open Scope rat_scope.
Check (1 + 1)%Q : rat.

(* eqtype.v:Delimit Scope eq_scope with EQ. *)
Open Scope eq_scope.                (* 通常は省略時解釈のまま使う。 *)
Check (1 = 1)%EQ : Prop.

(* bigop.v:Delimit Scope big_scope with BIG. *)
Open Scope big_scope.               (* 通常は省略時解釈のまま使う。 *)
Check (\sum_(i < 2)i)%BIG : nat.

(* ssrbool.v:Delimit Scope bool_scope with B. *)
Open Scope bool_scope.              (* 通常は省略時解釈のまま使う。 *)
Check (true && true)%B : bool.

(* ssrfun.v:Delimit Scope pair_scope with PAIR. *)
Open Scope pair_scope.              (* 通常は省略時解釈のまま使う。 *)
Check (1, 1)%PAIR : (rat * rat)%type.

(* ssrint.v:Delimit Scope int_scope with Z. *)
Open Scope int_scope.
(* int は、+ - などはグローバルに定義されていない。 *)
Check (addz 1 1)%Z : int.

(* END *)
