(**
power(累乗)関数の例
*)

(**
#<a href="http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf">
A Gentle Introduction to Type Classes and Relations in Coq
</a>#

にある累乗を計算する関数の例です。
そこでは、2種類の累乗の定義 [power] と [binary_power_mult] が同じであるという定理 
[binary_power_mult_ok] を証明しています。

[power] は、冪指数による再帰を使った単純なもので、
[binary_power_mult] は、冪指数を2分割して計算するものです。

[power] が O(n) のオーダー であるのに対して、
[binary_power_mult] O(log2(n)) のオーダーです。

ここで、[power] を累乗の仕様と考えて、
より効率的であるが読みにくい [binary_power_mult] の検証をおこなうと考えます（p.3)。

なお、オリジナルの文献で、はモノイドの説明として整数で定義していますが、
ここでは簡単に自然数で定義するものとします。

このソースコードは、
#<a href="https://github.com/suharahiromichi/coq/blob/master/gitcrc/coq_program_binary_power.v">ここ</a>#
にあります。
*)

Set Implicit Arguments.
Require Import Arith.
Require Import Div2.
(** destruct_call, on_call, etc... *)
Require Import Program.

(**
仕様となるpower関数
*)

Fixpoint power (x : nat) (n : nat) : nat :=
  match n  with
    | 0 => 1
    | S p => x * (power x p)
  end.

(**
補題
*)

Lemma power_S : forall x n, x * power x n = power x (S n).
Proof.
  intros; simpl.
  now auto.
Qed.

Lemma power_x_plus :
 forall x n p, power x (n + p) =  power x n * power x p.
Proof.
  induction n as [| p IHp]; simpl.
  - now auto.
  - intro q; rewrite (IHp q); rewrite mult_assoc.
    now auto.
Qed.

Lemma power_of_square :
  forall x n, power (x * x) n = (power x n) * (power x n).
Proof.
  induction n; simpl.
  - now auto.
  - rewrite mult_assoc.
    rewrite IHn.
    pattern (x * power x n * x); rewrite mult_comm.
    rewrite mult_assoc.
    now rewrite mult_assoc.
Qed.

(**
binary_power_mult_ok を参考に

nが偶数の場合  *)

Lemma power_even_n acc x n :
  Even.even n -> acc * power (x * x) (div2 n) = acc * power x n.
Proof.
  intro e.
  rewrite power_of_square.
  destruct n.
  - now auto.
  - pattern (S n) at 3; replace (S n) with (div2 (S n) + div2 (S n)).
    + rewrite <- power_x_plus.
      now auto.
    + generalize (even_double _ e); intro H.
      now auto.
Qed.

(**
 nが奇数の場合 *)

Lemma power_odd_n acc x n :
  Even.odd n -> acc * x * power (x * x) (div2 n) = acc * power x n.
Proof.
  intros o.
  rewrite power_of_square.
  destruct n.
  - now inversion o.
  - pattern (S n) at 3; replace (S n) with (S (div2 (S n) + div2 (S n))).
    + rewrite mult_assoc.
      rewrite <- mult_assoc.
      rewrite <- power_x_plus.
      rewrite <- mult_assoc.
      rewrite power_S.
      now auto.
    + generalize (odd_double _ o); intro H.
      now auto.
Qed.

(**
[P a = (a = acc * power x n)] を証明します。
 *)

Program Fixpoint binary_power_mult (acc : nat) (x : nat) (n : nat) {measure n} :
  {a : nat | a = acc * power x n} :=
  match n with
    | 0 => acc
    | _ =>
      match (Even.even_odd_dec n) with
        | left _ =>
          binary_power_mult acc (x * x) (div2 n)
        | right _ =>
          binary_power_mult (acc * x) (x * x) (div2 n)
      end
  end.
(** n が 0 の場合 *)
Next Obligation.
  rewrite mult_1_r.
  now auto.
Defined.
(** n が 偶数の場合 *)
Next Obligation.
  apply lt_div2.
  now auto with arith.
Defined.
Next Obligation.
  unfold binary_power_mult_func_obligation_2.
  (** see Program.v *)
  destruct_call binary_power_mult.
  rewrite e; simpl.
  apply power_even_n.
  now auto.
Defined.
(** n が 奇数の場合 *)
Next Obligation.
  apply lt_div2.
  now auto with arith.
Defined.
Next Obligation.
  unfold binary_power_mult_func_obligation_4.
  (** see Program.v *)
  destruct_call binary_power_mult.
  rewrite e; simpl.
  apply power_odd_n.
  now auto.
Defined.

Definition binary_power (x : nat) (n : nat) :=
  binary_power_mult 1 x n.
  

(** 実行してみます。 *)

Compute power 5 3.                          (** ==> 125 *)

Compute ` (binary_power 5 3).               (** ==> 125 *)

(*
以下は予備

(*
Function コマンド
{order} である measure は f n の形式。
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt7.html
 *)
Require Import Recdef.

Function binary_power_mult' (acc : nat) (x : nat) (n : nat) {measure id n} : nat :=
  match n with
    | 0 => acc
    | _ =>
      match (Even.even_odd_dec n) with
        | left _ =>
          binary_power_mult' acc (x * x) (div2 n)
        | right _ =>
          binary_power_mult' (acc * x) (x * x) (div2 n)
      end
  end.
Proof.
  - intros. unfold id.
    apply lt_div2. now auto with arith.
  - intros. unfold id.
    apply lt_div2. now auto with arith.
Defined.
Print binary_power_mult'.

(* 
Program コマンド、Functionと互換の形式
 *)
Program Fixpoint binary_power_mult'' (acc : nat) (x : nat) (n : nat) {measure n} : nat :=
  match n with
    | 0 => acc
    | _ =>
      match (Even.even_odd_dec n) with
        | left _ =>
          binary_power_mult'' acc (x * x) (div2 n)
        | right _ =>
          binary_power_mult'' (acc * x) (x * x) (div2 n)
      end
  end.
Next Obligation.                            (* Obligation 1 *)
  apply lt_div2. now auto with arith.
Defined.
Next Obligation.                            (* Obligation 1 *)
  apply lt_div2. now auto with arith.
Defined.

 *)

(* END *)
