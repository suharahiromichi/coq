From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

Local Open Scope ring_scope.

(**
本資料は ``{poly R}`` が ringType であることまで扱うので、R も ringType とする。
*)
Variable R : ringType.
Variable (a b c x y z : R) (p q r d : {poly R}).

(**
# n乗根 (1の冪乗根) Root of Unity

n乗して1になる数。
 *)

Check 3.-unity_root : pred R.
Locate "n .-unity_root". (* := (root_of_unity n) : ring_scope (default interpretation) *)
Print root_of_unity. (* = fun (R : ringType) (n : nat) => root ('X^n - 1) *)

Check @unity_rootE R : forall (n : nat) (z : R), n.-unity_root z = (z ^+ n == 1).
Check @unity_rootP R : forall (n : nat) (z : R), reflect (z ^+ n = 1) (n.-unity_root z).

Goal 3.-unity_root (1 : R).
Proof.
  rewrite unity_rootE.
  (* 1 ^+ 3 == 1 *)
  by rewrite expr1n.
Qed.

Goal (1 : R) \in 3.-unity_root.
Proof.
  Check unfold_in : forall (T : Type) (x : T) (p : pred T), (x \in [eta p]) = p x.
  rewrite unfold_in.                        (* coq/theorem/ssr/ssrbool.v *)
  (* ('X^3 - 1).[1] == 0 *)
  rewrite !hornerE hornerXn.
  (* 1 ^+ 3 - 1 == 0 *)
  by rewrite expr1n subr_eq0.
Qed.

(**
# 原始n乗根 Primitive Root of Unity

i (< n) 乗しても1にならず、n乗してはじめて1になる数
 *)

Check 3.-primitive_root : pred R.
Locate "n .-primitive_root". (* := (primitive_root_of_unity n) : ring_scope (default interpretation) *)
Print primitive_root_of_unity. (* = fun (R : ringType) (n : nat) (z : R) => (0 < n)%N
                                  && [forall i, (i.+1).-unity_root z == (i.+1 == n)] *)

Section NUMBER.
  Variable R : numDomainType.

  Goal 2.-primitive_root (-1 : R).
  Proof.
    apply/andP.
    split=> //=.
    apply/forallP => /= i.
    rewrite unity_rootE.
    case: i.
    case; [| case] => //= _.
    - rewrite expr1.
      by rewrite eqNr oner_eq0.
  - rewrite expr2 mulNr mul1r opprK.
    by rewrite 2!eq_refl.
  Qed.
  
End NUMBER.

(* END *)
