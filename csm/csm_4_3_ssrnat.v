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

Standard Coq の S と pred を rename したもの。nosimpl ではないことに注意してください。

後述する .*2 (double) は nosimple です。csm_3_6_3_simpl.v に誤記がありました。
*)

Locate ".+1".           (* S n : nat_scope (default interpretation) *)
Print S.                (* Inductive nat : Set :=  O : nat | S : nat -> nat *)

Locate ".-1".    (* Nat.pred n : nat_scope (default interpretation) *)
Print Nat.pred.  (* Nat.pred = fun n : nat => match n with | 0 => n | u.+1 => u end *)

(**
重大な注意

n.+1.-1 = n は、無条件に成立するが、
n.-1.+1 = n は、n≧1 でなければならない。 0.-1.+1 = 0.+1 = 1 なので。
*)

Check succnK : forall n : nat, n = n.+1.-1.
Check prednK : forall n : nat, 0 < n -> n.-1.+1 = n.

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
 *)
Print nosimpl.        (* Notation nosimpl t := (let 'tt := tt in t) *)

(**
match や let: を関数の定義の中で使うと、simplが機能しないことを利用する。
（定義を展開unfoldすると、simplは機能することに注意）

https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#locking-unlocking
の後半 We found that 以降。
*)
Definition add1 := (match tt with tt => Nat.add end).
Definition add2 := (let: tt := tt in Nat.add).
Definition add3 := (let tt := tt in Nat.add). (* これは simpl される。 *)

(* どこの simpl で 左辺が2に簡約されるか。 *)
Goal add1 1 1 = 2. Proof. simpl. rewrite /add1. simpl. reflexivity. Qed.
Goal add2 1 1 = 2. Proof. simpl. rewrite /add2. simpl. reflexivity. Qed.
Goal add3 1 1 = 2. Proof. simpl. reflexivity. Qed.

(*
simpl (rewrite /=) は、簡約をするタクティクで simplification の略。
https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.simpl
In detail, the tactic simpl 以降。

simpl タクティクは、β簡約またはι簡約をおこなうが、ι簡約できる場合のみδ簡約する
（δ簡約によって展開することで、ι簡約できるようになった場合のみ、その関数をδ簡約する）
という性質を使う。以下の例を参照のこと：
*)

(* 単なるι簡約：常にできる。 *)
Goal (match 0 with 0 => 1 | _ => 1 end) = 1. Proof. simpl. reflexivity. Qed.
Goal (match tt with tt => 1 end) = 1. Proof. simpl. reflexivity. Qed.

(* δ簡約して、ι簡約：これはできる。 *)
Definition one1 (n : nat) := (match n with 0 => 1 | _ => 1 end).
Goal one1 0 = 1. Proof. simpl. reflexivity. Qed. (* 1 = 1 *)

(* ι簡約しないなら、δ簡約してくれない。 *)
Definition one2 (n : nat) := (match tt with tt => 1 end).
Goal one2 0 = 1. Proof. simpl. Admitted.    (* one2 0 = 1 *)

(**
## Standard Coq の関数に変換する。

次の補題が用意されている。 
Standard Coq の add, sub, mul にも 「+」「-」「*」 が用意されているが、
デフォルトではないので、%coq_nat と表示される。

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
# comparison 比較
*)

(**
## MathComp の比較（不等式）

leq m n := (m - n == 0) で定義されている。「<=」は leq の Notation である。

「<」はleqで定義されている。ltn は「<」で定義されている。
*)

Locate "m <= n".    (* leq m n : nat_scope (default interpretation) *)
Check leq : nat -> nat -> bool.
Print leq.          (* leq = fun m n : nat => m - n == 0 *)

Locate "m < n".  (* leq m.+1 n : nat_scope (default interpretation) *)
Check ltn : nat -> nat -> bool.
Print ltn.       (* [rel m n | m < n] *)

(**
MathComp の「<=」などの不等式はboolである。leq は、nosimpl でないので、done で証明できる。
 *)

(**
## Standard Coq の比較（不等式）
*)
Check le : nat -> nat -> Prop.
Check lt : nat -> nat -> Prop.
(*
Standard Coq の不等式は Prop であり、 <= と < は、%coq_nat と表示される。
Stadnard Coq の不等式は done できない。
 *)

(**
## 相互変換のための補題：leP と ltP

boolの不等式と、Propの不等式(%coq_nat)の相互変換は、leP と ltP を使う。
一旦 %coq_nat に変換すれば、Standard Coq の omega などが使用できる。
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

Locate "m <= n". (* leq m n : nat_scope (default interpretation) *)
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
## 場合分けのための補題： leqP と ltnP （これは覚えるべき補題）

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
# iter

(略)
*)


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

Lemma oddn2 n : odd n.+2 = odd n.
Proof. rewrite /=. by rewrite negbK. Qed.

Lemma oddn1 n : odd n.+1 = ~~ odd n.
Proof. done. Qed.
  
Lemma odd_pred n : 1 <= n -> odd n.-1 = ~~ odd n.
Proof.
  elim: n => [// | n IHn H].
    by rewrite succnK oddn1 negbK.
Qed.


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
# exponentiation, factorial
 *)

Locate "m ^ n".    (* expn m n : nat_scope (default interpretation) *)
Print expn.        (* expn = nosimpl expn_rec *)

Locate "n `!".  (* factorial n : nat_scope (default interpretation) *)
Print factorial.                    (* factorial = nosimpl fact_rec *)

(**
# ex_minn, ex_maxn

(略)
 *)


(**
# これだけは憶えておきたい補題

以下も参照してください；
https://staff.aist.go.jp/reynald.affeldt/ssrcoq/ssrnat_doc.pdf
*)

Section Lemmas.
  Variables m n p q : nat.
  
  Check add0n n : 0 + n = n.          (* left_id 0 addn *)
  Check addn0 n : n + 0 = n.          (* right_id 0 addn *)
  Check add1n n : 1 + n = n.+1.       (* .+2 から .+4 も使用可能である。 *)
  Check addn1 n : n + 1 = n.+1.
  Check addnn n : n + n = n.*2.
  Check addSn m n : m.+1 + n = (m + n).+1.
  Check addnS m n : m + n.+1 = (m + n).+1.
  Check addSnnS m n : m.+1 + n = m + n.+1.
  
  Check addnC m n : m + n = n + m.             (* commutative addn *)
  Check addnA m n p : m + (n + p) = m + n + p. (* associative addn *)
  Check addnCA m n p : m + (n + p) = n + (m + p). (* left_commutative addn *)
  Check addnAC m n p : m + n + p = m + p + n. (* right_commutative addn *)
  Check addnACA m n p q : m + n + (p + q) = m + p + (n + q). (* interchange addn addn *)
  Check addKn m n : m + n - m = n.             (* cancel (addn n) (subn^~ n) *)
  Check addnK m n : n + m - m = n.             (* cancel (addn^~ n) (subn^~ n) *)
  
  Check subnn n : n - n = 0.                (* self_inverse *)
  
  Check mul0n n : 0 * n = 0.                (* left_zero 0 muln *)
  Check muln0 n : n * 0 = 0.                (* right_zero 0 muln *)
  Check mul1n n : 1 * n = n.                (* left_id 1 muln *)
  Check muln1 n : n * 1 = n.                (* right_id 1 muln *)
  Check mul2n n : 2 * n = n.*2.
  Check muln2 n : n * 2 = n.*2.
  Check mulnn n : n * n = n ^ 2.
  Check mulSn m n : m.+1 * n = n + m * n.
  Check mulSnr m n : m.+1 * n = m * n + n.
  Check mulnS m n : m * n.+1 = m + m * n.
  Check mulnSr m n : m * n.+1 = m * n + m.
  
  Check mulnC m n : m * n = n * m.             (* commutative muln *)
  Check mulnA m n p : m * (n * p) = m * n * p. (* associative muln *)
  Check mulnDl m n p : (m + n) * p = m * p + n * p. (* left_distributive muln addn *)
  Check mulnDr m n p : m * (n + p) = m * n + m * p. (* right_distributive muln addn *)
  Check mulnBl m n p : (m - n) * p = m * p - n * p. (* left_distributive muln subn *)
  Check mulnBr m n p : m * (n - p) = m * n - m * p. (* right_distributive muln subn *)
  Check mulnCA m n p : m * (n * p) = n * (m * p). (* left_commutative muln *)
  Check mulnAC m n p : m * n * p = m * p * n. (* right_commutative muln *)
  Check mulnACA m n p q : m * n * (p * q) = m * p * (n * q). (* interchange muln muln *)
End Lemmas.

(**
つぎの Search は結果がない（left_id で定義されているため）。
それらについては、ここで憶えてしまうしかない。
*)
Search _ (0 + _ = _).                       (* add0n は出てこない。 *)

(**
# 可換なとき、大きな式を扱うコツ

addn の場合

- ?addnA で左結合
- -?addnA で右結合

に変換できる。?は零回以上の繰り替えしで、すでにそうなっている場合にエラーにしないため。
*)

(**
## 3項を逆順にする。

1回の可換則では、隣どうししか入れ替えられないから、
3項を逆順にするには3回必要
*)
Goal 0 + 1 + 2 = 3.
Proof.
  rewrite ?addnA addnAC.                    (* 2番めを最後に *)
  rewrite -?addnA addnCA.                   (* 2番めを最初に *)
  rewrite ?addnA addnAC.                    (* 2番めを最後に *)
  done.
Qed.

(**
同上
 *)
Goal 0 + 1 + 2 = 3.
Proof.
  rewrite -?addnA addnCA.                   (* 2番めを最初に *)
  rewrite ?addnA addnAC.                    (* 2番めを最後に *)
  rewrite -?addnA addnCA.                   (* 2番めを最初に *)
  rewrite ?addnA.                           (* 左結合にする。 *)
  done.
Qed.

(**
## 項を入れ替える

任意の項を先頭または、最後にする方法。内容で項を指定する。

左結合で最後、右結合で先頭、にすれば、その項を取り出せる。
*)
Goal 0 + 1 + 2 + (3 + 4 + 5 + 6 + 7) + 8 + 9 = 45.
Proof.
  rewrite ?addnA.                           (* 左結合にする。 *)
  rewrite [_ + 4]addnC ?addnA.              (* 4 を先頭にする。 *)
  rewrite -?addnA.                          (* 右結合にする。 *)
  rewrite [6 + _]addnC -?addnA.             (* 6 を最後にする。 *)
  rewrite ?addnA.                           (* 左結合にする。 *)
  done.
Qed.

(* END *)
