(**
Coqで call/cc

2014_05_15 @suharahiromichi
*)

Require Import ssreflect ssrbool ssrnat seq.

(**
# 継続モナド

文献1.に紛れ込ませておいたcall/ccの定義を使ってみる。
今回も、例題は文献2.からいただいています。

## 定義
*)
Definition MCont R A := (A -> R) -> R.

Definition bind {R A : Type} (c : MCont R A)
           (f : A -> MCont R A) : MCont R A :=
  fun (k : A -> R) => c (fun (a : A) => f a k).

Definition ret {R A : Type} (a : A) : MCont R A :=
  fun k => k a.

(* call/cc、文献3の定義を参考にした。 *)
Definition callcc {R A B : Type}
           (f : (A -> MCont R B) -> MCont R A) : MCont R A :=
  fun (k : A -> R) => f (fun (a : A) => fun _ => k a) k.
Check callcc.
(**
    : ((A -> MCont R B) -> MCont R A) -> MCont R A

この型は古典論理のためのパースの公理と同じになる。。。

     ((A -> B) -> A) -> A
*)

(**
演算子と、do記法も定義しておく。
*)
Notation "c >>= f" :=
  (bind c f)
    (at level 42, left associativity).

Notation "s1 >> s2" :=
  (s1 >>= fun _ => s2)
    (at level 42, left associativity).

Notation "'DO' a <- A ; b <- B ; C 'OD'" :=
  (A >>= fun a => B >>= fun b => C)
    (at level 100, no associativity).

Notation "'DO' A ; B ; C 'OD'" :=
  (A >> B >> C)
    (at level 100, no associativity).

(**
# 例題

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
## flatten list

2次元リストを1次元にする。ただし、空リストがあったら空リストを返す（文献2.）。
*)

(**
### モナドを使わない定義
 *)
Fixpoint flatten_cps (l : seq (seq nat)) : MCont (seq nat) (seq nat) :=
  fun cont =>
    match l with
      | [::]      => cont [::]
      | [::] :: _ => [::]                   (* !! *)
      | x :: xs   => flatten_cps xs (fun y => cont (x ++ y))
    end.

Eval cbv in flatten_cps [:: [:: 1;2];[:: 3;4];[:: 5;6]] id.
Eval cbv in flatten_cps [:: [:: 1;2];[:: 3;4];[::];[:: 5;6]] id. (* [::] *)
Eval cbv in flatten_cps [:: [:: 1;2];[::];[:: 3;4];[:: 5;6]] id. (* [::] *)

(**
### モナドを使う定義
 *)
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
Eval cbv in flatten_callcc [:: [:: 1;2];[:: 3;4];[::];[:: 5;6]] id. (* [::] *)
Eval cbv in flatten_callcc [:: [:: 1;2];[::];[:: 3;4];[:: 5;6]] id. (* [::] *)

(**
# 文献

1. Coqで継続モナド
   http://qiita.com/suharahiromichi/items/f07f932103c28f36dd0e

2. お気楽 Haskell プログラミング入門 ●継続渡しスタイル
   http://www.geocities.jp/m_hiroi/func/haskell38.html

3. モナドのすべて Continuationモナド
   http://www.sampou.org/haskell/a-a-monads/html/contmonad.html
*)

(* END *)
