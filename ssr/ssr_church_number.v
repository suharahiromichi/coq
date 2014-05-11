(**
「リストは自分自身のfoldr関数として定義される」または、チャーチ数について
=========

2014_05_11 @suharahiromichi
 *)

(**
# はじめに

TAPL（参考文献1.)には、p.47とp.275の2箇所に渡って、
「リストは自分自身のfoldr関数として定義される」
と書かれているが、前後の説明を読んでも（リストのチャーチ表現は理解できるが）、
この一文の意味することはよくわからない。

また、別なところで、
「（System Fは）fixに頼ることなく純粋な言語でソート関数のようなものが書ける…」
と重要なことがさらりと書いてあったりもする（同 p.277）。

以下では、このふたつが同じことを言っていることを示す。
つまり、System Fの能力はチャーチ表現に基づいている、ということである。
*)

Require Import ssreflect ssrbool ssrnat.
Require Import ssrfun fintype finset.

(**
# チャーチ数

natとfoldnatを次のように定義する。
  *)

Inductive nat : Type :=
| O
| succ of nat.

Fixpoint foldnat (f : nat -> nat) (n : nat) : nat :=
  match n with
    | O => O
    | succ n' => f (foldnat f n')
  end.

Check foldnat.

(**
foldnat の型は以下である。

    foldnat : (nat -> nat) -> nat -> nat

(nat -> nat) -> nat -> nat のnatを全称∀で抽象（？）したものが、
チャーチ数（自然数のチャーチ表現）なのである。

    CNat = ∀X. (X -> X) -> X -> X
*)

(**
foldnat succ は何もしない関数になる。
*)

Check foldnat succ.
Eval compute in foldnat succ (succ (succ (succ O))).

(**
# 自然数のPair

PairNatとfoldpairnatを以下のように定義する。
*)

Inductive PairNat : Type :=
  pairNat of nat & nat.

Fixpoint foldpairnat (f : nat -> nat -> PairNat) (x : PairNat) : PairNat :=
  match x with
    | pairNat a b => f a b
  end.

Check foldpairnat.

(**
foldpairnat の型は以下である。

    foldpairnat : (nat -> nat -> PairNat) -> PairNat -> PairNat

「PairNat」を全称∀で抽象したものが、チャーチ表現になる。

    CPairNat = ∀X. (nat -> nat -> X) -> X -> X
*)

(**
foldpairnat pairNat は何もしない関数になる。
*)

Check foldpairnat pairNat. 
Eval compute in foldpairnat pairNat (pairNat (succ O) O).


(**
# 任意の型のPair

Pairとfoldpairを以下のように定義する。
*)

Inductive Pair (T : Type) : Type :=
  pair of T & T.

Fixpoint foldpair (T : Type) (f : T -> T -> Pair T) (x : Pair T) : Pair T :=
  match x with
    | pair a b => f a b
  end.

Check foldpair.

(**
foldpair の型は以下である。

    foldpair : (T -> T -> Pair T) -> Pair T -> Pair T

「Pair T」を全称∀で抽象したものが、チャーチ表現になる。

    CPair T = ∀X. (T -> T -> X) -> X -> X
*)

(**
foldpairnat pairNat は何もしない関数になる。
*)

Check foldpair nat (pair nat).
Eval compute in foldpair nat (pair nat) (pair nat (succ O) O).

(**
# リスト

Listとfoldrを以下のように定義する。
*)

Inductive List (X : Type) : Type :=
| nil
| cons of X & List X.

Fixpoint foldr (X : Type) (f : X -> List X -> List X) (l : List X) : List X :=
  match l with
    | nil => nil X
    | cons x l => f x (foldr X f l)
  end.

Check foldr.

(**
foldr の型は以下である。

    foldr : (X -> List X -> List X) -> List X -> List X

「List X」を全称∀で抽象したものが、チャーチ表現になる。

    CList X = ∀R. (X -> X -> R) -> R -> R
*)

(**
foldr cons は何もしない関数になる。
*)

Check foldr nat (cons nat).
Eval compute in foldr nat (cons nat) (cons nat O (cons nat O (nil nat))).

(* END *)
