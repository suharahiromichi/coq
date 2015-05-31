(**
プログラミング Coq 停止性が明らかでない関数を定義するには
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt7.html

練習問題をSSReflectに書き直した。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Definition tail (A : Type) (l : list A) :=
  match l with
    | nil => nil
    | a :: m => m
  end.

Check head 0 : seq nat -> nat.
Check last 0 : seq nat -> nat.
Check map (head 0) : seq (seq nat) -> seq nat.
Check @tail nat : seq nat -> seq nat.
Check map (@tail nat) : seq (seq nat) -> seq (seq nat).
Check @tail (seq nat) : seq (seq nat) -> seq (seq nat).
Check map (@tail (seq nat)) : seq (seq (seq nat)) -> seq (seq (seq nat)).
Check (fun (l : seq (seq nat)) => length (head nil l)).

Require Import Program.Wf.
(* measure の次の括弧が要る。 *)
Program Fixpoint transpose (l : seq (seq nat))
        {measure ((fun l => length (head nil l)) l)} : seq (seq nat) :=
  match l with
    | nil => nil
    | nil :: _ => nil
    | (x :: xs) :: xss =>
      map (head 0) l :: transpose (map (@tail nat) l)
  end.
(* No obligations *)

Check transpose : seq (seq nat) -> seq (seq nat).
Eval compute in transpose [:: [::11; 12; 13]; 
                            [:: 21; 22; 23; 24];
                            [:: 31; 32]].
(*  [:: [:: 11; 21; 31]; [:: 12; 22; 32]; [:: 13; 23; 0]] *)

Require Import Recdef.
(* measure の次の括弧がいらない。 *)
Function transpose' (l : seq (seq nat))
         : seq (seq nat) :=
  match l with
    | nil => nil
    | nil :: _ => nil
    | (x :: xs) :: xss =>
      map (head 0) l :: transpose (map (@tail nat) l)
  end.
(*
Proof.
  move=> l l' xss x xs //= H1 H2.
  subst.
  elim: xs => [| a l //= H].
  - by [].
  - apply/ltP.
    by rewrite ltnS ltnSn.
Defined.
*)

Check transpose' : seq (seq nat) -> seq (seq nat).
Eval compute in transpose' [:: [::11; 12; 13]; 
                            [:: 21; 22; 23; 24];
                            [:: 31; 32]].
(*  [:: [:: 11; 21; 31]; [:: 12; 22; 32]; [:: 13; 23; 0]] *)

(* END *)
