From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
keen さん 幽霊型を知った

https://keens.github.io/blog/2015/05/24/yuureikatawoshitta/
*)

Inductive exp :=
| Nat   of nat
| Bool  of bool
| If    of exp * exp * exp
| Plus  of exp * exp
| Equal of exp * exp.


(*
Inductive phantom {T : Type} := Phantom of exp.
Inductive phantom {T : Type} :=
| Phantom (a : exp) : phantom.
*)
(*
Inductive texp {T : Type} := E of exp. *)
Inductive texp {T : Type} :=
| E (a : exp) : texp.

Definition mkNat (x : nat) : @texp nat := E (Nat x).     (* Nat x *)
Definition mkBool (x : bool) : @texp bool := E (Bool x). (* Bool x *)
Definition mkIf (A : Type) (Ecmd : @texp bool) (Ethn Eels : @texp A) : @texp A :=
  match Ecmd, Ethn, Eels with
  | E cmd, E thn, E els => E (If (cmd, thn, els))
  end.
Definition mkPlus (Ea Eb : @texp nat) : @texp nat :=
  match Ea, Eb with
  | E a, E b => E (Plus (a, b))
  end.
Definition mkEqual (T : Type) (Ea Eb : @texp T) : @texp bool :=
  match Ea, Eb with
  | E a, E b => E (Equal (a, b))
  end.

Check mkNat 1 : texp.
Check mkBool true : texp.
Check mkIf (mkBool true) (mkNat 1) (mkNat 2) : texp.
Check mkIf (mkBool true) (mkBool false) (mkBool true) : texp.
Check mkPlus (mkNat 1) (mkNat 2) : texp.
Check mkEqual (mkNat 1) (mkNat 2) : texp.
Check mkEqual (mkBool true) (mkBool true) : texp.

Fail Check mkPlus (mkBool true) (mkNat 1).
Fail Check mkPlus (mkBool true) (mkBool true).
Fail Check mkIf (mkNat 1) (mkNat 1) (mkNat 2). (* 第1引数はboolであること。 *)
Fail Check mkIf (mkBool true) (mkNat 1) (mkBool true). (* 第2と第3引数が同じ型であること。 *)

(* mkNat と mkBool でなく、コアーションを使う例 *)

Coercion E : exp >-> texp.
Coercion Nat : nat >-> exp.
Coercion Bool : bool >-> exp.

Definition a : @texp nat := 1.
Definition b : @texp bool := true.
Check mkPlus a a.
Fail Check mkPlus a b.


(* 単位を含める例 *)

Inductive Time := Hour | Min | Sec.
Inductive tnat {T : Time} := F of nat.
Definition tadd (T : Time) (x y : @tnat T) : @tnat T := (* x と y と返り値の T は同じ。 *)
  match x, y with
  | F x', F y' => F (x' + y')
  end.
Definition tadd2 (T : Time) (x y : @tnat T) : @tnat T := (* x と y と返り値の T は同じ。 *)
  match x, y with
  | @F _ x', @F _ y' => F (x' + y')         (* 型をマッチ節で受けられないらしい。 *)
  end.

(* これ以降、F は意識しないでよい。 *)
Coercion F : nat >-> tnat.

Definition a : @tnat Hour := 2.
Definition b : @tnat Sec  := 3.

Check tadd a a.
Fail Check tadd a b.

(* END *)
