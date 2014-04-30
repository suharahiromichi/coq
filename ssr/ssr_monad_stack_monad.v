(**
「スタックモナド」でスタック計算機を作る
========

@suharahiromichi 2014_02_01

Stack Monad を使ってスタック計算機を定義してみて、
スタックモナドの使い方の実例を示す。

また、スタックを使った演算の複数の定義が同じ結果になることを示す。
本当にモナドになっていることも示す。
証明は SSReflect を使っておこなう。
 *)

Require Import ssreflect ssrbool ssrnat seq eqtype ssrfun.

(**
# Stack Monad

Stack Monad は State Monad のひとつで、
Stackという「状態」を関数型言語から使いやすくするものである。
*)

(**
## スタックモナド Stack Monad の定義

スタックは seq nat (natのリスト) で表す。
「->」の右が直積になっているのは、
スタックをpopした結果を置くためである。
また、後でモナド則を証明するために、T型にしている。
*)
Definition MStack (T : Type) :=
  seq nat -> (T * seq nat).

(**
## スタックをpush,popする関数

スタック (MStack nat) 型の関数を定義する。
*)
Definition push : nat -> MStack nat :=
  fun n : nat =>
    fun q : seq nat =>
      (0, n :: q).

Definition pop : MStack nat :=
  fun q : seq nat =>
    match q with
      | n :: q' => (n, q')
      | _ => (0, q)
    end.

(**
空のスタックを作る関数も用意する。
 *)
Definition empty : MStack nat :=
  fun _ => (0, [::]).

(**
## スタックモナド Stack Monad の基本演算
*)
Definition ret {T : Type} : T -> MStack T :=
  fun n : T => fun q : seq nat => (n, q).

(**
bind (>>=) は右結合で、優先順位は(=)より強い。(=)の有線順位は70)
 *)
Definition bind {T S : Type} : MStack T -> (T -> MStack S) -> MStack S :=
  fun s : MStack T =>
    fun c : T -> MStack S =>
      fun q : seq nat =>
        let (n, q') := s q in c n q'.
Infix ">>=" := bind (right associativity, at level 61).

(**
(>>) は右結合で、(>>=)と同じ優先順位とする。
 *)
Definition bind2 {T S : Type} : MStack T -> MStack S -> MStack S :=
  fun s1 : MStack T =>
    fun s2 : MStack S =>
      s1 >>= fun _ => s2.
Infix ">>" := bind2 (right associativity, at level 61).

(**
### おまけの関数

以下は、モナド則の証明だけに使うので、「_」を付けた名前にする。
*)

Definition id_ {T : Type} (v : T) : T := v.

Definition fmap_ {T S : Type} (f : T -> S) (mx : MStack T) : MStack S :=
  mx >>= (fun x => ret (f x)).

Definition join_ {T : Type} (s : MStack (MStack T)) : MStack T :=
  s >>= id_.

(**
### do記法
*)

Notation "'do' [ a <- A ; B ]" :=
  (A >>= fun a => B)
    (at level 100, right associativity).
Notation "'do' [ a <- A ; b <- B ; C ]" :=
  (A >>= fun a => B >>= fun b => C)
    (at level 100, right associativity).
Notation "'do' [ a <- A ; b <- B ; c <- C ; D ]" :=
  (A >>= fun a => B >>= fun b => C >>= fun c => D)
    (at level 100, right associativity).
Notation "'do' [ a <- A ; b <- B ; c <- C ; d <- D ; E ]" :=
  (A >>= fun a => B >>= fun b => C >>= fun c => D >>= fun d => E)
    (at level 100, right associativity).

(**
# 演算のいろいろな定義

前節で用意した関数を使って、実際に加減乗の演算を定義してみる。
 *)

(**
## 直接定義する方法

加減乗算をスタック (MStack nat) を使って直接定義する。
*)
Definition binary_op2 (op : nat -> nat -> nat) : MStack nat :=
  fun q : seq nat =>
    match q with
      | n :: m :: q' => (0, (op m n) :: q')
      | _ => (0, [::0])
    end.
Definition SPlus2 := binary_op2 plus.
Definition SMinus2 := binary_op2 minus.
Definition SMult2 := binary_op2 mult.

(**
## push, popだけで定義する方法

モナドの基本演算を使わないで定義する。
*)
Definition binary_op1 (op : nat -> nat -> nat) : MStack nat :=
  fun q : seq nat =>
    let (n, q') := pop q in
    let (m, q'') := pop q' in
    push (op m n) q''.
Definition SPlus1 := binary_op1 plus.
Definition SMinus1 := binary_op1 minus.
Definition SMult1 := binary_op1 mult.

(**
## モナドの基本演算 bind, ret を使う方法

モナドの基本演算を使って定義する。
*)
Definition binary_op (op : nat -> nat -> nat) : MStack nat :=
  pop >>=
      fun n => pop >>=                      (* n は後にpushしたもの。 *)
                   fun m => push (op m n).  (* m は先にpushしたもの。 *)
Definition SPlus : MStack nat := binary_op plus.
Definition SMinus : MStack nat := binary_op minus.
Definition SMult : MStack nat := binary_op mult.

(**
## do記法を使う方法

モナドの基本演算、ただし、do記法を使って定義する。
*)

Definition binary_op' (op : nat -> nat -> nat) : MStack nat :=
  do [ n <- pop;
       m <- pop;
       push (op m n) ].
Definition SPlus' : MStack nat := binary_op' plus.
Definition SMinus' : MStack nat := binary_op' minus.
Definition SMult' : MStack nat := binary_op' mult.

(**
# 実行例
*)

(**
3 + (5 - 2) = 6 を実行してみる。
 *)
Eval compute in
    empty >> push 3 >> push 5 >> push 2 >> SMinus >> SPlus >> pop.
Eval compute in
    empty >> push 3 >> push 5 >> push 2 >> SMinus1 >> SPlus1 >> pop.
Eval compute in
    empty >> push 3 >> push 5 >> push 2 >> SMinus2 >> SPlus2 >> pop.
Eval compute in
    empty >> push 3 >> push 5 >> push 2 >> SMinus' >> SPlus' >> pop.

(**
# 演算の定義が等しいことの証明

SPlus を使った計算と SPlus1 を使った計算が同じことを証明する。
*)
Goal forall n m,
       empty >> push n >> push m >> SPlus >> pop =
       empty >> push n >> push m >> SPlus1 >> pop.
Proof.
    by [].
Qed.

Goal SPlus = SPlus1.
    by [].
Qed.

(**
SPlus を使った計算と SPlus2 を使った計算が同じことを証明する。
*)
Goal forall n m,
       empty >> push n >> push m >> SPlus >> pop =
       empty >> push n >> push m >> SPlus2 >> pop.
Proof.
    by [].
Qed.

Eval compute in SPlus [::].
Eval compute in SPlus1 [::].
Eval compute in SPlus2 [::].

Goal forall s : seq nat, SPlus1 s = SPlus2 s.
Admitted.

Goal SPlus1 = SPlus2.
Admitted.

(**
# ifelse

ここでは使わないが、Postscript風の ifelse の定義は以下のようになる。
*)
Definition ifelse (s1 : MStack nat) (s2 : MStack nat) : MStack nat :=
  pop >>= fun n => if n == 0 then s2 else s1.

Eval compute in
    push 1 >> ifelse (push 0) (push 1) >> pop.

(**
do記法を使うと以下のようになる。
*)
Definition ifelse' (s1 : MStack nat) (s2 : MStack nat) : MStack nat :=
  do [ n <- pop;
       if n == 0 then s2 else s1 ].

(**
# モナド則の証明

スタックモナドがモナド則を満たすことを証明しておく。

## functional_extensionality を使う場合

関数が等しいことを示す公理 ∀q. f q = g q -> f = g を導入する必要がある。
 *)

Axiom functional_extensionality :
  forall {T : Type},
  forall {f g : MStack T},
    (forall (q : seq nat), f q = g q) -> f = g.

(**
### モナド則 その1
 *)
Theorem monad_1 :
  forall (T S : Type),
  forall (f : T -> MStack S) (n : T),
    ret n >>= f = f n.
Proof.
    by [].
Qed.
  
(**
### モナド則 その2
 *)
Theorem monad_2 :
  forall (T : Type),
  forall (s : MStack T),
    s >>= ret = s.
Proof.
  move=> T s.
  apply: functional_extensionality.
  move=> q.
  rewrite /bind /ret.
    by elim: s.
Qed.

(**
### モナド則 その3
 *)
Theorem monad_3 :
  forall (T S R : Type),
  forall (f : T -> MStack S) (g : S -> MStack R) (s : MStack T),
    (s >>= f) >>= g =
    s >>= (fun n => f n >>= g).
Proof.
  move=> T S R f g s.
  apply: functional_extensionality.
  move=> q.
  rewrite /bind.
    by elim: s.
Qed.

(**
## 可換図式を証明する

### 結合則
 *)
Theorem assoc_law :
  forall (T : Type) (s : MStack (MStack (MStack T))),
    join_ (join_ s) = join_ ((fmap_ join_) s).
Proof.
  move => T s.
  rewrite /join_ /fmap_ /ret.
    by rewrite ! monad_3.
Qed.

(**
### 左単位元
 *)
Theorem unit_left_law :
  forall (T : Type) (s : MStack (MStack T)),
    join_ (ret s) = id_ s.
Proof.
  move => T s.
  rewrite /join_.
    by rewrite monad_1.
Qed.

(**
### 右単位元
 *)
Theorem unit_right_law :
  forall (T : Type) (m : MStack (MStack T)),
    join_ ((fmap_ ret) m) = id_ m.
Proof.
  move=> A m.
  rewrite /join_ /fmap_ /id_.
  by rewrite monad_3 monad_2.
Qed.

(**
## 「=1」での成立を示す

SSReflectでは、ssrfun.vで
functional_extensionality のもとで関数が同じことを示す等号
「=1」が導入されている。
「=」の代わりに「=1」を使うと、
公理functional_extensionalityを追加する必要がなくなる。
このほうが、SSReflectらしいのだろう。
 *)

Theorem monad_1' :
  forall (T S : Type),
  forall (f : T -> MStack S) (n : T),
    ret n >>= f =1 f n.
Proof.
    by [].
Qed.

Theorem monad_2' :
  forall (T : Type),
  forall (s : MStack T),
    s >>= ret =1 s.
Proof.
  move=> T s q.
  rewrite /bind /ret.
    by elim: s.
Qed.

Theorem monad_3' :
  forall (T S R : Type),
  forall (f : T -> MStack S) (g : S -> MStack R) (s : MStack T),
    (s >>= f) >>= g =1 s >>= (fun n => f n >>= g).
Proof.
  move=> T S R f g s q.
  rewrite /bind.
    by elim: s.
Qed.

(**
# 補足

## do 記法の別の定義
*)

Notation "'do' a <- A ; B" :=
  (A >>= fun a => B)
    (at level 100, right associativity).

Definition binary_op'' (op : nat -> nat -> nat) : MStack nat :=
  do n <- pop;
  do m <- pop;
  push (op m n).

(**
# 参考

1. Haskellでスタックを利用した加減乗除の計算機を作ってみる
   http://kzfm.github.io/laskell/stackCalc.html

2. ソフトウェアの基礎 単純な命令型プログラム 練習問題 stack_compiler
   http://proofcafe.org/sf/Imp_J.html
 *)

(* $Id: ssr_monad_stack_monad.v,v 1.42 2014/04/30 09:20:34 suhara Exp suhara $ *)
