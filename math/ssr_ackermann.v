From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import FunInd.                      (* Functional Scheme *)
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

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

Section Pr.

  Variable T : Type.
  
  Fixpoint pr (n : nat) (f g : T -> T) : T -> T :=
    match n with
    | 0 => f
    | n'.+1 => g \o (pr n' f g)
    end.

(*
  (pr 0 f g) x = f x
  (pr 1 f g) x = g (f x)
  (pr 2 f g) x = g (g (f x)).
*)

End Pr.

Section Ack2.
(**
ack' f 0 = f 1
ack' f 1 = f (f 1)
ack' f 2 = f (f (f 1))
*)
  
  Definition ack' (f : nat -> nat) (m : nat) : nat :=
    (pr m f f) 1.

  Compute ack' S 10.                        (* 12 *)

(**
ここまでは正しそう。。。。。
 *)

  Section Test.
    Variable m : nat.

    Check fun m => m.+1.                            (* n = 0 *)
    Check ack' (fun m => m.+1) m.                   (* n = 1 *)
    Check ack' (fun m => ack' (fun m => m.+1) m) m. (* n = 2 *)
  End Test.
  Compute (ack' (fun m => m.+1) 2).         (* n = 1, m = 2, 4 *)
  Compute (ack' (fun m => ack' (fun m => m.+1) m)) 3. (* n = 2, m = 3, 9 *)
  
  Check ack' (ack' (fun m => m.+1)).
  Compute (ack' (ack' (fun m => m.+1))) 3.  (* 9 *)


  Fixpoint pr2 (n : nat) (f : nat -> nat) (g : (nat -> nat) -> nat -> nat) :=
    match n with
    | 0 => f
    | n'.+1 => g (pr2 n' f g)
    end.

  Definition ack n m :=
    (pr2 n (fun m => m.+1) ack') m.

  Compute ack 1 2.                          (* 4 *)
  Compute ack 2 3.                          (* 9 *)

End Ack2.

(* END *)
