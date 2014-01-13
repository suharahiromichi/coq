(** Monadic Task Combinators *)
(** モナディック タスク コンビネータ *)

(* @suharahiromichi 2014_01_13 *)

Require Import ssreflect ssrbool ssrnat seq eqtype.
Require Import ssrfun.
Require Import String.                      (* Error *)

(* スケジュラー *)
Inductive time : Set :=
Time of nat.

Inductive fd : Set :=
Fd of nat.

Inductive sched : Set :=                    (* TBD *)
| sleep_ of time                            (* 時間待ち *)
| read_ of fd                               (* fd待ち *)
| write_ of fd & string.
(* 実行中を示すReadyを追加するべきだ。 *)

Definition thunk := list sched.

(** Option と Error *)
Inductive optionE (T : Type) : Type :=
  | SomeE : T -> optionE T
  | NoneE : string -> optionE T.

Implicit Arguments SomeE [[T]].
Implicit Arguments NoneE [[T]].

(** タスク コンビネータ *)
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
Check sleep_ (Time 1).
Check SomeE (1, (sleep_ (Time 1))).
Check SomeE (1, (sleep_ (Time 1)) :: nil).

Definition sleep (time : nat) : task unit :=
  fun (u : thunk) =>
    SomeE (tt, (sleep_ (Time time)) :: u).  (* timeだけsleepして、unitを返す。 *)

Definition read (fd : nat) : task unit :=
  fun (u : thunk) =>
    SomeE (tt, (read_ (Fd fd)) :: u).       (* fdからreadする。 *)

Definition write (fd : nat) (s : string) : task unit :=
  fun (u : thunk) =>
    SomeE (tt, (write_ (Fd fd) s) :: u).

(* タスクの合成 *)
Definition test (fd : nat) : task unit :=
  loop 10
       ((read 1 >>> sleep 10)
          >*<
          (write 1 "test" >>> sleep 10)).
Eval compute in test 1.
(* これでは、>>>と>*<の区別無く、ひとつのリストになってしまう。 *)

(* タスクの実行 *)
Definition one (us : thunk) : thunk :=
  match us with
    | [::] => [::]
    | u :: us' => us'   (* ここでは、左から順に実行するが、 *)
(*  | u :: us' => u :: us'  ... 終了しなれば、uを戻してもよい。 *)
  end.

Fixpoint run (step : nat) (us : thunk) : thunk :=
  match step with
    | 0 => us
    | S steps' =>
      run steps' (one us)
  end.

Definition main :=
  match test 1 [::] with                    (* [::]は、初期状態の空のthunk *)
    | SomeE (x, u) => run 100 u
    | NoneE err => [::]
  end.

(* END *)
