(**
Coqで call/cc

2014_05_15 @suharahiromichi
*)

Require Import ssreflect ssrbool ssrnat seq.

(**
# 継続モナド

## 定義
*)
Definition MCont R A := (A -> R) -> R.

Definition ret {R A : Type} (a : A) : MCont R A :=
  fun k => k a.

Definition bind {R A : Type} (c : MCont R A)
           (f : A -> MCont R A) : MCont R A :=
  fun (k : A -> R) => c (fun (a : A) => f a k).

Infix ">>=" := bind (left associativity, at level 42).

Definition bind2 {R A : Type} (s1 s2 : MCont R A) : MCont R A :=
  s1 >>= fun _ => s2.

Infix ">>" := bind2 (left associativity, at level 42).

Notation "'DO' a <- A ; b <- B ; C 'OD'" :=
  (A >>= fun a => B >>= fun b => C)
    (at level 100, right associativity).

Notation "'DO' A ; B ; C 'OD'" :=
  (A >> B >> C)
    (at level 100, right associativity).

Definition callcc {R A : Type}
           (f : (A -> MCont R A) -> MCont R A) : MCont R A :=
  fun (k : A -> R) => f (fun (a : A) => fun _ => k a) k.

(**
## 大域脱出の例（文献2.）
 *)
Definition bar1 (cont : nat -> MCont nat nat) := ret 1 : MCont nat nat.
Definition bar2 (cont : nat -> MCont nat nat) := cont 2 : MCont nat nat.
Definition bar3 (cont : nat -> MCont nat nat) := ret 3 : MCont nat nat.

Definition foo (cont : nat -> MCont nat nat) :=
  DO
    bar1 cont;
    bar2 cont;                              (* !! *)
    bar3 cont
  OD.

Definition test := callcc (fun k => foo k) id.
Eval cbv in test.                           (* 2 *)

(**
## flatten

2次元リストを1次元にする。ただし、空リストがあったら空リストを返す（文献2.）。
*)

Fixpoint flatten_cps (l : seq (seq nat)) : MCont (seq nat) (seq nat) :=
  fun cont =>
    match l with
      | [::]      => cont [::]
      | [::] :: _ => [::]                   (* !! *)
      | x :: xs   => flatten_cps xs (fun y => cont (x ++ y))
    end.

Eval cbv in flatten_cps [:: [:: 1;2];[:: 3;4];[:: 5;6]] id.
Eval cbv in flatten_cps [:: [:: 1;2];[:: 3;4];[::];[:: 5;6]] id.
Eval cbv in flatten_cps [:: [:: 1;2];[::];[:: 3;4];[:: 5;6]] id.


Fixpoint flatten' (k : seq nat -> MCont (seq nat) (seq nat))
         (l : seq (seq nat)) : MCont (seq nat) (seq nat) :=
  match l with
    | [::]      => ret [::]
    | [::] :: _ => k [::]                   (* !! *)
    | x :: xs   => flatten' k xs >>= fun y => ret (x ++ y)
  end.

Definition flatten_callcc (l : seq (seq nat)) : MCont (seq nat) (seq nat) :=
  callcc (fun (k : seq nat -> MCont (seq nat) (seq nat)) => flatten' k l).

Eval cbv in flatten_callcc [:: [:: 1;2];[:: 3;4];[:: 5;6]] id.
Eval cbv in flatten_callcc [:: [:: 1;2];[:: 3;4];[::];[:: 5;6]] id.
Eval cbv in flatten_callcc [:: [:: 1;2];[::];[:: 3;4];[:: 5;6]] id.

(**
# 文献

1. Library lc.Monad
   http://coq.inria.fr/pylons/contribs/files/lc/trunk/lc.Monad.html

2. お気楽 Haskell プログラミング入門 ●継続渡しスタイル
   http://www.geocities.jp/m_hiroi/func/haskell38.html
*)

(* END *)

