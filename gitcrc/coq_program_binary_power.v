Set Implicit Arguments.
Require Import Arith.
Require Import Div2.

Fixpoint power (x : nat) (n : nat) : nat :=
  match n  with
    | 0 => 1
    | S p => x * (power x p)
  end.

(*
Function コマンド
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt7.html
 *)
Require Import Recdef.
Function binary_power_mult (acc : nat) (x : nat) (n : nat) {measure id n} : nat :=
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
(*
2 subgoals, subgoal 1 (ID 132)
  
  ============================
   nat ->
   nat ->
   forall n n0 : nat,
   n = S n0 ->
   forall e : Even.even (S n0),
   Even.even_odd_dec (S n0) = left e -> id (div2 (S n0)) < id (S n0)

subgoal 2 (ID 133) is:
 nat ->
 nat ->
 forall n n0 : nat,
 n = S n0 ->
 forall o : Even.odd (S n0),
 Even.even_odd_dec (S n0) = right o -> id (div2 (S n0)) < id (S n0)
*)
Proof.
  intros. unfold id.
  apply lt_div2. now auto with arith.
Proof.
  intros. unfold id.
  apply lt_div2. now auto with arith.
Defined.
Print binary_power_mult.

(* 
Program コマンド
http://d.hatena.ne.jp/airobo/20120813/1344837154

私が便利だと思っているのは Program Fixpoint です．何が便利かというと，（coercion の自動挿入
も嬉しいのですが，）induction の measure として，複数の引数が使えることです．例えば，nat
-> nat -> nat 型の再帰関数を定義しようとしたときに，Function の measure関数は一引数関数しか
許されていないので，uncurry化した nat * nat -> nat 型の関数を一度定義した後に curry化してや
る必要があります．

 *)
Require Import Program.                     (* destruct_call, on_call, etc... *)
Program Fixpoint binary_power_mult' (acc : nat) (x : nat) (n : nat) {measure n} : {x : nat | True} :=
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
Next Obligation.                            (* Obligation 1 *)
  apply lt_div2. now auto with arith.
Defined.
Next Obligation.                            (* Obligation 1 *)
  apply lt_div2. now auto with arith.
Defined.

(**
https://coq.inria.fr/distrib/current/refman/Reference-Manual026.html

23.1.2  Program Definition ident := term.
Variants:
1. Program Definition ident :term1 := term2.
It interprets the type term1, potentially generating proof obligations to be
resolved. Once done with them, we have a Coq type term1′. It then checks that the type of
the interpretation of term2 is coercible to term1′, and registers ident as being of type
term1′ once the set of obligations generated during the interpretation of term2 and the
aforementioned coercion derivation are solved.
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

Lemma power_x_plus :
 forall x n p, power x (n + p) =  power x n *  power x p.
Proof.
  admit.
Qed.

Lemma power_of_square :
  forall x n, power (x * x) n = (power x n) * (power x n).
Proof.
  admit.
Qed.

(* binary_power_mult_ok を参考に *)
Lemma power_even_n acc x n :
  Even.even n -> acc * power (x * x) (div2 n) = acc * power x n.
Proof.
  intro Hen.
  rewrite power_of_square.
  destruct n.
  - auto.
  - pattern (S n) at 3; replace (S n) with (div2 (S n) + div2 (S n))%nat; auto.
    + rewrite <- power_x_plus; auto.
    + generalize (even_double _ Hen); intro H; auto.      
Qed.

Lemma power_one x :
  x = power x 1.
Proof.
  admit.
Qed.

Lemma power_odd_n acc x n :
  Even.odd n -> acc * x * power (x * x) (div2 n) = acc * power x n.
Proof.
  intros Hon.
  rewrite power_of_square.
  destruct n.
  - admit.
  - pattern (S n) at 3; replace (S n) with (S (div2 (S n) + div2 (S n)))%nat; auto.
    rewrite mult_assoc.
    generalize (odd_double _ Hon); intro H; auto.
    + rewrite <- mult_assoc.
      rewrite <- power_x_plus.
      rewrite <- mult_assoc.
      replace (S n) with (div2 (S n) + div2 (S n)).
      * admit.
      * admit.
Qed.


Program Fixpoint binary_power_mult''' (acc : nat) (x : nat) (n : nat) {measure n} :
  {a : nat | a = acc * power x n} :=
  match n with
    | 0 => acc
    | _ =>
      match (Even.even_odd_dec n) with
        | left _ =>
          binary_power_mult''' acc (x * x) (div2 n)
        | right _ =>
          binary_power_mult''' (acc * x) (x * x) (div2 n)
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
  unfold binary_power_mult'''_func_obligation_2.
  unfold eq_ind_r.
  unfold eq_ind.
  unfold eq_rect.
  simpl.
  destruct_call binary_power_mult'''.
  simpl.
  rewrite e.
  apply power_even_n.
  auto.
Defined.
Next Obligation.                            (* 奇数 *)
  apply lt_div2. now auto with arith.
Defined.
Next Obligation.                            (* 奇数 *)
  unfold binary_power_mult'''_func_obligation_4.
  destruct_call binary_power_mult'''.
  rewrite e.
  simpl.
  apply power_odd_n.
  auto.
Defined.

(* END *)
