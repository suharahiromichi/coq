(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.3 ssrnat.v --- SSReflect 向け nat 型のライブラリ

======

2018_12_02 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ssrbool.v のソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/ssrnat.v
*)

(**
# successor and predecessor

Standard Soq の S と pred を rename したもの。nosimpl ではないことに注意してください。

次節にある .*2 (double) は nosimple です。csm_3_6_3_simpl.v に誤記がありました。
*)

Locate ".+1".           (* S n : nat_scope (default interpretation) *)
Print S.                (* Inductive nat : Set :=  O : nat | S : nat -> nat *)

Locate ".-1".    (* Nat.pred n : nat_scope (default interpretation) *)
Print Nat.pred.  (* Nat.pred = fun n : nat => match n with | 0 => n | u.+1 => u end *)


(**
nat_eqType、eqType のインスタンス
*)

Check 1 : nat_eqType : eqType.
Check 1 : nat        : Type.

(**
# bin_nat, number

(略)
*)


(**
# basic arithmetic

## 定義

Standard Soq の Nat.add, Nat.sub. Nat.mul に nosimpl をつけたもの。
*)

Locate "m + n".    (* addn m n : nat_scope (default interpretation) *)
Print addn.        (* addn = nosimpl addn_rec *)
Print addn_rec.    (* Nat.add *)
Print plus.        (* Notation plus := Nat.add (Standard Coq での定義) *)

Locate "m - n".    (* subn m n : nat_scope (default interpretation) *)
Print subn.        (* subn = nosimpl subn_rec *)
Print subn_rec.    (* subn_rec = Nat.sub *)
Print minus.       (* Notation minus := Nat.sub (Standard Coq での定義) *)

Locate "m * n".    (* muln m n : nat_scope (default interpretation) *)
Print muln.        (* muln = nosimpl muln_rec *)
Print muln_rec.    (* muln_rec = Nat.mul *)
Print mult.        (* Notation mult := Nat.mul (Standard Coq での定義) *)

(**
## nosimpl とは

定義のなかで（これが重要）match や let: を使うと、simplが機能しない。

simpl (rewrite /=) は、簡約をするタクティクで simplification の略。
*)

Definition add1 := (match tt with tt => Nat.add end).
Definition add2 := (let: tt := tt in Nat.add).
Definition add3 := (let tt := tt in Nat.add). (* これは simpl される。 *)

(* どこの simpl で 左辺が2に簡約されるか。 *)
Goal add1 1 1 = 2. Proof. simpl. rewrite /add1. simpl. reflexivity. Qed.
Goal add2 1 1 = 2. Proof. simpl. rewrite /add2. simpl. reflexivity. Qed.
Goal add3 1 1 = 2. Proof. simpl. reflexivity. Qed.


(**
## Standard Coq の関数に変換する。

次の補題が用意されている。 
Standard Coq の add, sub, mul には + * / が用意されているが、
デフォルトでないので、%coq_nat と表示される。

一旦 %coq_nat に変換すれば、Standard Coq の omega などが使用できる。
ただし、ltacで定義するのが現実的である。ssr_omega.v 参照のこと。
*)

Check plusE  : Nat.add = addn.
Check minusE : Nat.sub = subn.
Check multE  : Nat.mul = muln.

Goal 1 + 1 = 2. Proof. rewrite -plusE. simpl. reflexivity. Qed. (* (1 + 1)%coq_nat *)
Goal 1 - 1 = 0. Proof. rewrite -minusE. simpl. reflexivity. Qed. (* (1 - 1)%coq_nat *)
Goal 1 * 1 = 1. Proof. rewrite -multE. simpl. reflexivity. Qed. (* (1 * 1)%coq_nat *)


(**
# comparison
*)

Locate "m <= n".    (* leq m n : nat_scope (default interpretation) *)
Print leq.          (* leq = fun m n : nat => m - n == 0 *)

(**
MathComp の <= などの不等式はboolである。Prop の不等式にしたい場合は、
leP と ltP を使う。

leq は、nosimpl でないので、done で証明できる。
Standard Coq の <= と < は、Prop なので done できなくなる。
*)

Goal forall n, n <= n.+1.
Proof.
  move=> n.
  apply/leP.
  (* (n <= n.+1)%coq_nat *)
  Fail done.                     (* done で終わらない。 *)
  apply/leP.
  (* n <= n.+1 *)  
  done.
Qed.

Goal forall n, n < n.+1.
Proof.
  move=> n.
  apply/ltP.
  (* (n < n.+1)%coq_nat *)
  done.
Qed.  


Locate "m < n".  (* leq m.+1 n : nat_scope (default interpretation) *)
Locate "m >= n". (* leq n m : nat_scope (default interpretation) *)
Locate "m > n".  (* leq n.+1 m : nat_scope (default interpretation) *)

(* <= 以外は、Notation である。 *)
(* そのため、< を使っていなくても、m.+1 <= n が m < n と表示される場合がある。 *)
(* 以下のように、< が一番よく使われるので、おどろかないようにする。 *)
Check 1 <= 2.                               (* 0 < 2 *)
Check 2 >= 1.                               (* 0 < 2 *)
Check 0 <= 1.                               (* 0 <= 1 *)
Check 1 >= 0.                               (* 0 <= 1  *)

(**
場合分けのための補題： leqP と ltnP （これは覚えるべき補題）。

(leP と ltP と紛らわしいが、別なもの）
*)

Goal forall m n, (if m <= n then n else m) = maxn n m.
Proof.
  move=> m n.
  rewrite /maxn.
    by case: leqP.
Qed.    
(* if then else は = より結合度が低いので、括弧がいる。 *)

Goal forall m n, (if m <= n then m else n) = minn n m.
Proof.
  move=> m n.
  rewrite /minn.
    by case: ltnP.
Qed.    

(**
# min, max
*)

Print minn.       (* minn = fun m n : nat => if m < n then m else n *)
Print maxn.       (* maxn = fun m n : nat => if m < n then n else m *)

(* 当然、可換である。 *)
Goal forall m n, minn m n = minn n m.
Proof.
  move=> m n.
    by rewrite minnC.
Qed.

Goal forall m n, n <= m -> minn n m = n.
Proof.
  move=> m n.
  rewrite /leq.
  move/eqP.
  rewrite minnE.
  move=> ->.
    by rewrite subn0.
Qed.

Goal forall m n, n <= m -> maxn m n = m.
Proof.
  move=> m n.
  rewrite /leq.
  move/eqP.
  rewrite maxnE.
  move=> ->.
    by rewrite addn0.
Qed.


(**
# parity

odd は 「odd(n.+1) -> ~~ odd(n)」 という再帰で定義されている。
なので、odd か even (= not odd) の証明は、単純な数学的帰納法で証明できる。
 *)

Print odd.
(* 
odd = 
fix odd (n : nat) : bool := match n with
                            | 0 => false
                            | n'.+1 => ~~ odd n'
                            end
 *)

(**
# doubling, halving
 *)

Locate ".*2".      (* double n : nat_scope (default interpretation) *)
Print double.      (* double = nosimpl double_rec *)

Locate "./2".        (* half n : nat_scope (default interpretation) *)
Print half.          (* half = 
                        fix half (n : nat) : nat := match n with
                            | 0 => n
                            | n'.+1 => uphalf n'
                            end
                            with uphalf (n : nat) : nat := match n with
                               | 0 => n
                               | n'.+1 => (half n').+1
                               end *)


(**
これに対して Standard Coq の even は even(n.+2) -> even(n) の帰納法なので、
非標準な帰納法が必要になってしまう。

csm_3_5_elim.v も参照せよ。
 *)

Print Nat.even.
(* 
Nat.even = 
fix even (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | n'.+2 => even n'
  end
 *)



(**
# exponentiation, factorial
 *)

Locate "m ^ n".    (* expn m n : nat_scope (default interpretation) *)
Print expn.        (* expn = nosimpl expn_rec *)

Locate "n `!".  (* factorial n : nat_scope (default interpretation) *)
Print factorial.                    (* factorial = nosimpl fact_rec *)



(*   A (infix) -- conjunction, as in                                          *)
(*      ltn_neqAle : (m < n) = (m != n) && (m <= n).                          *)
(*   B -- subtraction, as in subBn : (m - n) - p = m - (n + p).               *)
(*   D -- addition, as in mulnDl : (m + n) * p = m * p + n * p.               *)
(*   M -- multiplication, as in expnMn : (m * n) ^ p = m ^ p * n ^ p.         *)
(*   p (prefix) -- positive, as in                                            *)
(*      eqn_pmul2l : m > 0 -> (m * n1 == m * n2) = (n1 == n2).                *)
(*   P  -- greater than 1, as in                                              *)
(*      ltn_Pmull : 1 < n -> 0 < m -> m < n * m.                              *)
(*   S -- successor, as in addSn : n.+1 + m = (n + m).+1.                     *)
(*   V (infix) -- disjunction, as in                                          *)
(*      leq_eqVlt : (m <= n) = (m == n) || (m < n).                           *)
(*   X - exponentiation, as in lognX : logn p (m ^ n) = logn p m * n in       *)
(*         file prime.v (the suffix is not used in ths file).                 *)

(* END *)
