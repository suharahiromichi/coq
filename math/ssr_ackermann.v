(**
アッカーマン Ackermann 関数は、
高階原始帰納的関数（primitive recursiveな汎関数）として定義できる。
*)

(**
課題；
CCC (CPL) による実装はある。
チャーチ・エンコーディングの元で実装できるか。System Fでは。
*)

From mathcomp Require Import all_ssreflect.
(*
Require Import ssromega.
Require Import FunInd.                      (* Functional Scheme *)
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(**
# Coq での定義
*)
Module Ack1.

  Fail Fixpoint ack_bad (n m : nat) : nat :=
    match n with
    | 0 => S m
    | n'.+1 =>
      match m with
      | 0 => ack_bad n' 1
      | m'.+1 => ack_bad n' (ack_bad n m')
      end
    end.

(**
https://www.iij-ii.co.jp/activities/programming-coq/coqt7.html
*)
  Fixpoint ack' (f : nat -> nat) (m : nat) : nat :=
    match m with
    | 0 => f 1
    | m'.+1 => f (ack' f m')
    end.
  
  Fixpoint ack (n m : nat) : nat :=
    match n with
    | 0 => m.+1
    | n'.+1 => ack' (ack n') m
    end.

End Ack1.

Compute Ack1.ack' S 10.                     (* 12 *)
Compute Ack1.ack 1 2.                       (* 4 *)
Compute Ack1.ack 2 3.                       (* 9 *)
Compute Ack1.ack 3 4.                       (* 125 *)

(**
# 原始帰納法

pr2のほうが使いやすいが、prのほうが圏論的には正しい？
*)
Section Pr.

  Variable T : Type.
  
  Fixpoint pr (n : nat) (f g : T -> T) : T -> T :=
    match n with
    | 0 => f
    | n'.+1 => g \o (pr n' f g)
    end.
(**
   (pr 0 f g) x = f x
   (pr 1 f g) x = g (f x)
   (pr 2 f g) x = g (g (f x)).
*)

  Fixpoint pr2 (n : nat) (x : T) (g : T -> T) : T :=
    match n with
    | 0 => x
    | n'.+1 => g (pr2 n' x g)
    end.
(**
   pr2 0 x g = x
   pr2 1 x g = g x
   pr2 2 x g = g (g x).
*)
End Pr.

(**
# 高階原始帰納法による Ackermann 関数の定義

高階原始帰納的関数（primitive recursiveな汎関数）として定義する。
*)
Section Ack2.
(**
ack' f 0 = f 1
ack' f 1 = f (f 1)
ack' f 2 = f (f (f 1))

ack' は pr でも pr2 でも定義できるが。
*)
  Definition ack' (f : nat -> nat) (m : nat) : nat := (pr m f f) 1.
  Definition ack'' (f : nat -> nat) (m : nat) : nat := pr2 m (f 1) f.
  Check ack'' : (nat -> nat) -> nat -> nat.
  
  Compute ack' S 10.                        (* 12 *)
  Compute ack'' S 10.                       (* 12 *)
  

(**
ack は pr2 でないと難しい。
*)
  Definition ack n m := (pr2 n S ack'') m.
  Check ack : nat -> nat -> nat.

  Compute ack 1 2.                          (* 4 *)
  Compute ack 2 3.                          (* 9 *)
  Compute ack 3 4.                          (* 125 *)
  
End Ack2.

(**
System F の Church Encodeing
*)
Module ChurchNat.
  
  Definition CNat := forall (X : Set), (X -> X) ->  X -> X.

  Definition czero : CNat := fun X f x => x.
  Definition csucc (N : CNat) : CNat := fun X f x => f (N X f x).  
  
  Definition cplus' (M N : CNat) : CNat := M CNat csucc N. (* 1 を M回足す *)
  Definition cmult' (M N : CNat) : CNat := M CNat (cplus' N) czero. (* N を M回足す *)

  Definition ack' (f : CNat -> CNat) (M : CNat) : CNat := M CNat f (f (csucc czero)).
  Check ack' : (CNat -> CNat) -> CNat -> CNat.

  (* 引数にとれるのは、CNat -> CNat の関数だけ。 *)
  Fail Definition ack (M : CNat) := M CNat ack' csucc.

  (* Mを高階にすればしのげるが。。。 *)
  Definition CNatNat := forall (X : Set), ((X -> X) -> (X -> X)) -> (X -> X) -> (X -> X).
  Check ack' (ack' csucc) : CNat -> CNat.

  Definition ack (M : CNatNat) := M CNat ack' csucc.
  Check ack : CNatNat -> CNat -> CNat.

  (* 引数にわたせない。  *)
  
  Fail Compute ack (csucc czero) (csucc (csucc czero)).

End ChurchNat.


Section Th.

  Lemma test n m : Ack1.ack n m = ack n m.
  Proof.
    elim: n m => //= n IHn m.
  Admitted.

End Th.

(* END *)
