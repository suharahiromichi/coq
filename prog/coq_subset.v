(**
Subset Type と Program コマンド
 *)

Require Import Bool.
Require Import List.
Require Import Omega.
Require Import Program.
Set Implicit Arguments.

(** * はじめに *)

(**
自然数を(+ 1)する関数 succ を考えてみます。
 *)

Definition succ' (x : nat) : nat := x + 1.

(**
これは自然数から自然数の関数
 *)

Check succ' : nat -> nat.

(**
でまちがいありませんが、
詳しくみると、値域は自然数全体ではなく、「1 以上の自然数」つまり自然数のサブセットです。

Coqでは、これを次のように書きます。「1 以上の自然数の型」という意味になります。
*)

Check {y : nat | 1 <= y} : Type.

(**
これを使って、(+ 1)する関数 succ を定義しなおすと、次のようになります。

Program コマンドを使うと、nat 型である [x + 1] から、
上記のサブセットへのコアーションが自動的に行われます。

また、[1 <= x + 1] を証明することを求められます（証明責務）ので、[omega] で解きます。
  *)

Program Definition succ (x : nat) : {y : nat | 1 <= y} :=
  x + 1.
Obligation 1.
Proof.
  (* Goal : 1 <= x + 1 *)
  omega.
Defined.

(**
(+ 2)する関数をsuccをふたつ使って定義すると、次のようになります。

ここでもコアーションが行われています。
また、こんども証明責務は [omega] で解けます。
  *)

Program Definition succsucc (x : nat) : {y : nat | 2 <= y} :=
  succ (succ x).
Obligation 1.
Proof.
  (* 2 <= x + 1 + 1 *)
  omega.
Defined.

(**
実行すると、つぎのようになります。演算子「`」については後述します。
 *)

Compute ` (succ 3).                         (** ==> 4 *)

Compute ` (succsucc 3).                     (** ==> 5 *)


(** * Subset タイプ *)

(** * 「Program」コマンド *)

(* END *)
