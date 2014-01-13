(** Monadic Task Combinators *)
(** モナディック タスク コンビネータ *)

(* @suharahiromichi 2014_01_13 *)

Require Import ssreflect ssrbool ssrnat seq eqtype.
Require Import ssrfun.
Require Import String.                      (* Error *)

(** Option と Error *)
Inductive optionE (T : Type) : Type :=
  | SomeE : T -> optionE T
  | NoneE : string -> optionE T.

Implicit Arguments SomeE [[T]].
Implicit Arguments NoneE [[T]].

(** タスク コンビネータ *)
Inductive sched : Set :=
.                                           (* TBD *)
Definition thunk := list sched.

Definition task (T : Type) :=
  thunk -> optionE (T * thunk).
Print unit.
Check unit.
Check (task unit).
Check (task nat).

(* ret : T -> task T *)
Definition ret {T : Type} (x : T) : task T :=
  fun (u : thunk) => SomeE (x, u).
Check ret 1.

(* bind : task T -> (T -> task S) -> task S *)
Definition bind_ {T S : Type} (p : task T) (f : T -> task S) : task S :=
  fun (u : thunk) =>
    match p u with
      | SomeE (x, u') => f x u'
      | NoneE err => NoneE err
    end.
Infix ">>=" := bind_ (left associativity, at level 71).

(* bind2 : task T -> task S -> task S *)
Definition bind2_ {T S : Type} (p1 : task T) (p2 : task S) : task S :=
  p1 >>= fun _ => p2.
Infix ">>>" := bind2_ (left associativity, at level 71).

(* bind1 : task T -> task S -> task T *)
Definition bind1_ {T S : Type} (p1 : task T) (p2 : task S) : task T :=
  p1 >>= fun x => p2 >>> ret x.
Infix "<<<" := bind1_ (left associativity, at level 71).

(* or : task T -> task T -> task T *)
Definition or_ {T : Type} (p1 p2 : task T) : task T :=
  fun (u : thunk) =>
    match p1 u with
      | SomeE t => SomeE t
      | NoneE err1 =>
        match p2 u with
          | SomeE t => SomeE t
          | NoneE err2 => NoneE (err1 ++ err2) (* エラー文字列の連結 *)
        end
    end.
Infix "<|>" := or_ (left associativity, at level 71).

(* and : task T -> task S -> task (T * S) *)
Definition and_ {T S : Type} (p1 : task T) (p2 : task S) : task (T * S) :=
  p1
    >>= fun x => p2
                   >>= fun y => ret (x, y).
Infix ">*<" := and_ (left associativity, at level 71).

(* many : task T -> task (list T)、結果をリストで返す。 *)
Fixpoint many {T : Type} (steps : nat) (p : task T) : task (list T) :=
  match steps with
    | 0 => 
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      (p                                    (* ここの括弧は必要！ *)
         >>= fun x => many steps' p
                           >>= fun u => ret (x :: u))
      <|>
      ret [::]
  end.

(* loop : task T -> task unit、結果を返さない。 *)
Fixpoint loop {T : Type} (steps : nat) (p : task T) : task unit :=
  match steps with
    | 0 => 
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      (p                                    (* ここの括弧は必要！ *)
         >>= fun x => loop steps' p)
      <|>
      ret tt
  end.

(* タスク部品 *)
Definition sleep (time : nat) : task unit :=
  ret tt.                                   (* timeだけsleepして、unitを返す。 *)

Definition read (fd : nat) : task nat :=
  ret fd.                                   (* fdからreadして、 fdを返す。*)

Definition write (fd : nat) (s : string) : task nat :=
  ret fd.

(* タスクの合成 *)
Definition test (fd : nat) : task unit :=
  loop 10
       ((read 1 >>> sleep 10)
          >*<
          (write 1 "test" >>> sleep 10)).

(* タスクの実行 *)
(* TBD *)

(* END *)
