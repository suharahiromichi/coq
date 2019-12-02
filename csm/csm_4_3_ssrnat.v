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

standard coq の S と pred を rename したもの。
nosimpl ではないことに注意してください。

次節にある .*2 (double) は nosimple です。
csm_3_6_3_simpl.v に誤記がありました。
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

nosimpl がついている。

csm_3_6_3_simpl.v も参照のこと。
*)

Locate "m + n".    (* addn m n : nat_scope (default interpretation) *)
Print addn.        (* addn = nosimpl addn_rec *)

Locate "m - n".    (* subn m n : nat_scope (default interpretation) *)
Print subn.        (* subn = nosimpl subn_rec *)

Locate "m * n".    (* muln m n : nat_scope (default interpretation) *)
Print muln.        (* muln = nosimpl muln_rec *)

(**
# comparison
*)

Locate "m <= n".    (* leq m n : nat_scope (default interpretation) *)
Print leq.          (* leq = fun m n : nat => m - n == 0 *)

(**
MathComp の <= などの不等式はboolである。Prop の不等式にしたい場合は、
leP と ltP を使う。

leq は、nosimpl でないので、done で証明できる。
むしろ、Standard Coq の <= と < にすると、Prop なので done できなくなる。
*)

Goal forall n, n <= n.+1.
Proof.
  move=> n.
  apply/leP.
  (* (n <= n.+1)%coq_nat *)
  (* done で終わらない。やってみて。 *)
  apply/leP.
  (* n <= n.+1 *)  
  done.
Qed.

Goal forall n, n < n.+1.
Proof.
  move=> n.
  apply/ltP.
  (* (n < n.+1)%coq_nat *)
  (* done で終わらない。やってみて。 *)
  apply/leP.
  (* n < n.+1 *)  
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
