(** Stack Monad *)
(** 「スタックモナド」でスタック計算機を作ってみる。*)
(* State Monad のひとつ。 *)
(** @suharahiromichi 2014_02_01 *)

Require Import ssreflect ssrbool ssrnat seq eqtype ssrfun.

(** スタックモナド Stack Monad の定義 *)
Definition Stack := seq nat -> nat * seq nat.

(** 主要な関数の定義  *)
Definition ret : nat -> Stack :=
  fun n : nat => fun q : seq nat => (n, q).

Definition bind : Stack -> (nat -> Stack) -> Stack :=
  fun s : Stack =>
    fun c : nat -> Stack =>
      fun q : seq nat =>
        let (n, q') := s q in c n q'.
Infix ">>=" := bind (right associativity, at level 61).
(** 右結合で、優先順位は = より強い。(=は70)  *)

Definition bind2 : Stack -> Stack -> Stack :=
  fun s1 : Stack =>
    fun s2 : Stack =>
      s1 >>= fun _ => s2.
Infix ">>" := bind2 (right associativity, at level 61).

(** スタック処理の関数  *)
Definition push : nat -> Stack :=
  fun n : nat =>
    fun q : seq nat =>
      (0, n :: q).

Definition pop : Stack :=
  fun q : seq nat =>
    match q with
      | n :: q' => (n, q')
      | _ => (0, q)
    end.

(** 空のスタックを作る。 *)
Definition empty : Stack :=
  fun _ => (0, [::]).

(** 二項演算のいろいろな定義 *)
(** 直接定義する方法 *)
Definition binary_op2 (op : nat -> nat -> nat) : Stack :=
  fun q : seq nat =>
    match q with
      | n :: m :: q' => (0, (op m n) :: q')
      | _ => (0, q)
    end.
Definition SPlus2 := binary_op2 plus.
Definition SMinus2 := binary_op2 minus.
Definition SMult2 := binary_op2 mult.

(** push, pop を使う方法 *)
Definition binary_op1 (op : nat -> nat -> nat) : Stack :=
  fun q : seq nat =>
    let (n, q') := pop q in
    let (m, q'') := pop q' in
    push (op m n) q''.
Definition SPlus1 := binary_op1 plus.
Definition SMinus1 := binary_op1 minus.
Definition SMult1 := binary_op1 mult.

(** bind, ret も使う方法 *)
Definition binary_op (op : nat -> nat -> nat) : Stack :=
  pop >>=
      fun n => pop >>=                      (* n は後にpushしたもの。 *)
                   fun m => push (op m n).  (* m は先にpushしたもの。 *)
Definition SPlus : Stack := binary_op plus.
Definition SMinus : Stack := binary_op minus.
Definition SMult : Stack := binary_op mult.

(** 実行例 *)
(** 3 + (5 - 2) = 6 *)
Eval compute in
    empty >> push 3 >> push 5 >> push 2 >> SMinus >> SPlus >> pop.
Eval compute in
    empty >> push 3 >> push 5 >> push 2 >> SMinus1 >> SPlus1 >> pop.
Eval compute in
    empty >> push 3 >> push 5 >> push 2 >> SMinus2 >> SPlus2 >> pop.

(** SPlus を使った計算と SPlus1 を使った計算が同じことを証明する。 *)
Goal forall n m,
       empty >> push n >> push m >> SPlus >> pop =
       empty >> push n >> push m >> SPlus1 >> pop.
Proof.
  done.
Qed.

(** SPlus を使った計算と SPlus2 を使った計算が同じことを証明する。 *)
Goal forall n m,
       empty >> push n >> push m >> SPlus >> pop =
       empty >> push n >> push m >> SPlus2 >> pop.
Proof.
  done.
Qed.

(** モナド則を証明する。 *)
Axiom functional_extensionality :
  forall {f g : Stack},
    (forall (q : seq nat), f q = g q) -> f = g.

(** モナド則 その1 *)
Theorem monad_1 :
  forall (f : nat -> Stack) (n : nat),
    ret n >>= f = f n.
Proof.
  done.
Qed.
  
(** モナド則 その2 *)
Theorem monad_2 :
  forall (s : Stack),
    s >>= ret = s.
Proof.
  move=> s.
  apply: functional_extensionality.
  move=> q.
  rewrite /bind /ret.
  destruct s.
  done.
Qed.

(** モナド則 その3 *)
Theorem monad_3 :
  forall (f g : nat -> Stack) (s : Stack),
    (s >>= f) >>= g =
    s >>= (fun n => f n >>= g).
Proof.
  move=> f g s.
  apply: functional_extensionality.
  move=> q.
  rewrite /bind.
  destruct s.
  done.
Qed.

(** 補足：SSReflect的には、
functional_extensionality を使わずに、
「=1」での成立をいうのがよいだろうか？ *)
Theorem monad_1' :
  forall (f : nat -> Stack) (n : nat),
    ret n >>= f =1 f n.
Proof.
  done.
Qed.

Theorem monad_2' :
  forall (s : Stack),
    s >>= ret =1 s.
Proof.
  move=> s q.
  rewrite /bind /ret.
  destruct s.
  done.
Qed.

Theorem monad_3' :
  forall (f g : nat -> Stack) (s : Stack),
    (s >>= f) >>= g =1
    s >>= (fun n => f n >>= g).
Proof.
  move=> f g s q.
  rewrite /bind.
  destruct s.
  done.
Qed.

(* END *)

(** 参考：
kzfm さん
Haskellでスタックを利用した加減乗除の計算機を作ってみる
http://kzfm.github.io/laskell/stackCalc.html
 *)
