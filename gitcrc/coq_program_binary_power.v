(* 
Program Definition ident : { x : Type | P x } := term. の形式の定義について。

https://coq.inria.fr/distrib/current/refman/Reference-Manual026.html
 *)

Set Implicit Arguments.
Require Import Arith.
Require Import Div2.
Require Import Recdef.
Require Import Program.                     (* destruct_call, on_call, etc... *)

(* P x = (x = n) *)
Program Fixpoint id' (n : nat) : {x | x = n} := n.


(* http://mattam.org/repos/coq/fingertrees/src/examples.v *)
(* P x = (n = 2 * x \/ n = 2 * x + 1) *)
Program Fixpoint div2' (n : nat) : 
  { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
  match n with
    | S (S p) => S (div2' p)
    | x => 0
  end.

Next Obligation.
Proof.
  case o; intro H.
  - left.
    now rewrite H; auto.
  - right.
    f_equal; rewrite H.
    rewrite plus_0_r.
    pattern (x + S x); rewrite plus_comm.
    now rewrite plus_Sn_m.
Defined.

Next Obligation.
  destruct n ; simpl in * ; intuition.
  destruct n ; simpl in * ; intuition.
  elim (H n) ; auto.
Qed.
Print id'.

(*
仕様となるpower関数
*)
Fixpoint power (x : nat) (n : nat) : nat :=
  match n  with
    | 0 => 1
    | S p => x * (power x p)
  end.

(*
Function コマンド
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt7.html
 *)
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

(* 
Program コマンド、{x | P x} の形式
 *)
Lemma double_2x x : x + x = double x.
Proof.
  now unfold double.
Qed.

Lemma power_S : forall x n, x * power x n = power x (S n).
Proof.
  intros; simpl; auto.
Qed.

Lemma power_x_plus :
 forall x n p, power x (n + p) =  power x n *  power x p.
Proof.
  induction n as [| p IHp]; simpl.
  - now auto.
  - now intro q; rewrite (IHp q); rewrite mult_assoc.
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

(* binary_power_mult_ok を参考に *)
Lemma power_even_n acc x n :
  Even.even n -> acc * power (x * x) (div2 n) = acc * power x n.
Proof.
  intro e.
  rewrite power_of_square.
  destruct n.
  - auto.
  - pattern (S n) at 3; replace (S n) with (div2 (S n) + div2 (S n))%nat; auto.
    + rewrite <- power_x_plus; auto.
    + generalize (even_double _ e); intro H; auto.      
Qed.

Lemma power_odd_n acc x n :
  Even.odd n -> acc * x * power (x * x) (div2 n) = acc * power x n.
Proof.
  intros o.
  rewrite power_of_square.
  destruct n.
  - now inversion o.
  - pattern (S n) at 3; replace (S n) with (S (div2 (S n) + div2 (S n)))%nat; auto.
    + rewrite mult_assoc.
      generalize (odd_double _ o); intro H; auto.
      rewrite <- mult_assoc.
      rewrite <- power_x_plus.
      rewrite <- mult_assoc.
      now rewrite power_S.
    + rewrite double_2x.
      rewrite <- (odd_double (S n)); auto.
Qed.

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
Next Obligation.                            (* 0 *)
  rewrite mult_1_r.
  auto.
Defined.
Next Obligation.                            (* 偶数 *)
  apply lt_div2. now auto with arith.
Defined.
Next Obligation.                            (* 偶数 *)
  unfold binary_power_mult_func_obligation_2.
  unfold eq_ind_r.
  unfold eq_ind.
  unfold eq_rect.
  simpl.
  destruct_call binary_power_mult.
  simpl.
  rewrite e.
  apply power_even_n.
  auto.
Defined.
Next Obligation.                            (* 奇数 *)
  apply lt_div2. now auto with arith.
Defined.
Next Obligation.                            (* 奇数 *)
  unfold binary_power_mult_func_obligation_4.
  destruct_call binary_power_mult.
  rewrite e.
  simpl.
  apply power_odd_n.
  auto.
Defined.

(* END *)


(**
http://d.hatena.ne.jp/airobo/20120813/1344837154

私が便利だと思っているのは Program Fixpoint です．何が便利かというと，（coercion の自動挿入
も嬉しいのですが，）induction の measure として，複数の引数が使えることです．例えば，nat
-> nat -> nat 型の再帰関数を定義しようとしたときに，Function の measure関数は一引数関数しか
許されていないので，uncurry化した nat * nat -> nat 型の関数を一度定義した後に curry化してや
る必要があります．
*)


