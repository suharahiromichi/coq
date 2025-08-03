(**
無限長2進数とルーラー関数

see also. coq4/prog4/ssr_binary.v
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ssrZ zify ring lra.
(* opam install coq-equations *)
From Equations Require Import Equations.
Import Arith.                               (* Nat.land_spec *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.                        (* ssralg.v *)
Import Num.Def Num.Theory.                  (* ssrnum.v *)
Import intZmod.

Open Scope ring_scope.

(**
# 無限長2進数の世界

2進数でも任意の自然数・整数・有理数を表現できる。

.1111111…      = 1     小数点が左端
…1111111.      = -1    小数点が右端
…111.111…      = 0     小数点が途中 (2進実数)

この話のポイントは、補数表現は有限の桁数（8ビットで256を法とするなど）に限らないことである。
とりあえず、整数を扱う。
 *)

(**
# 問題 ``x & (- x)`` の意味

負数とビット単位での論理積をとる。

結城浩「数学ガールの秘密のノート ビットとバイナリー」


0001 1111      0001              1      1       0
0010 1110      0010              2      2       1
0011 1101      0001              3      1       0
0100 1100      0100              4      4       2
0101 1011      0001              5      1       0
0110 1010      0010              6      2       1
0111 1001
1000 1000      1000              8      8       3
*)


(**
# mathcomp の ssrint

ここでは、mathcomp の int を使う。
Standard Rocq (Coq) とは異なるが、Lean も同じ定義である。
*)

Print int.
(*
Variant int : Set :=
| Posz : nat -> int
| Negz : nat -> int.
*)

Compute Posz 2.                             (* = 2%Z *)
Compute Posz 1.                             (* = 1%Z *)
Compute Posz 0.                             (* = 0%Z *)
Compute Negz 0.                             (* = (-1)%Z *)
Compute Negz 1.                             (* = (-2)%Z *)
Compute Negz 2.                             (* = (-3)%Z *)

(* Negz のほうの定義が判りにくい。Leanでは… *)

Lemma negz_m__minus_n1 (m : nat) : Negz m = - m.+1%:Z.
Proof.
  done.
Qed.

Lemma negzm_1__minus_m (m : nat) : (0 < m)%nat -> Negz m.-1 = - m%:Z.
Proof.
  by case: m.
Qed.

(**
## oppz (- x) 負数
*)

Section opp_test.
  Variable n : nat.
  Print oppz.
  Compute oppz (Posz 0).                    (* = 0%Z *)
  Compute oppz (Posz n.+1).                 (* = Negz n *)
  Compute oppz (Negz n).                    (* = Posz n.+1 *)
End opp_test.

(**
# Standard coq の自然数 (PeanoNat) の bitwise 計算

MathComp であっても、Standard Rocq (Coq) で定義された自然数のbitwize計算は全て使える。
モジュール名 ``Nat.`` を付けること。
 *)
Print Nat.testbit.
(*
fix testbit (a n : nat) {struct n} : bool :=
  match n with
  | 0%N => Nat.odd a
  | n0.+1 => testbit (Nat.div2 a) n0
  end
     : nat -> nat -> bool
*)

Check Nat.land_spec
  : forall a b n : nat, Nat.testbit (Nat.land a b) n = Nat.testbit a n && Nat.testbit b n.
Check Nat.lor_spec
  : forall a b n : nat, Nat.testbit (Nat.lor a b) n = Nat.testbit a n || Nat.testbit b n.
Check Nat.lxor_spec
  : forall a b n : nat, Nat.testbit (Nat.lxor a b) n = xorb (Nat.testbit a n) (Nat.testbit b n).
Check Nat.ldiff_spec
  : forall a b n : nat, Nat.testbit (Nat.ldiff a b) n = Nat.testbit a n && ~~ Nat.testbit b n.

(* ビット毎の論理否定が普通の形で定義されていない。なぜでしょうか。 *)
Print Nat.lnot.                             (* 桁数の指定が要る。 *)
Print Nat.ones.                             (* 桁数の指定が要る。 *)

(**
# 整数 int のbitwise計算

本題にはいります。mathcomp にないので自分で定義します。
*)

Section bitwise.
(**
## not

自然数の not (ビットワイズの反転) は定義できないが、
整数の not は定義できる。
*)
  Definition lnot (x : int) : int :=
    match x with
    | (Posz n) => Negz n
    | (Negz n) => Posz n
    end.
  Compute lnot 2.                           (* = (-3)%Z *)
  Compute lnot 1.                           (* = (-2)%Z *)
  Compute lnot 0.                           (* = (-1)%Z *)
  Compute lnot (-1).                        (* = 0%Z *)
  Compute lnot (-2).                        (* = 1%Z *)
  Compute lnot (-3).                        (* = 2%Z *)
  
  Definition lor (x y : int) : int :=
    match x, y with
    | (Posz m), (Posz n) => Posz (Nat.lor m n)   (* x | y *)
    | (Posz m), (Negz n) => Negz (Nat.ldiff n m) (* x | ~y = ~(~x & y) *)
    | (Negz m), (Posz n) => Negz (Nat.ldiff m n) (* ~x | y = ~(x & ~y) *)
    | (Negz m), (Negz n) => Negz (Nat.land m n)  (* ~x | ~y) = ~(x & y) *)
    end.
    
  (* この定義から 2025/8/23 ProorCafe *)
  (* Equations と mathcomp の併用は問題がある。 *)
  Definition land (x y : int) : int :=
    match x, y with
    | (Posz m), (Posz n) => Posz (Nat.land m n)  (* x & y *)
    | (Posz m), (Negz n) => Posz (Nat.ldiff m n) (* x & ~y *)
    | (Negz m), (Posz n) => Posz (Nat.ldiff n m) (* ~x & y *)
    | (Negz m), (Negz n) => Negz (Nat.lor m n)   (* ~x & ~y = ~(x | y) *)
    end.
  
  Definition lxor (x y : int) : int :=
    match x, y with
    | (Posz m), (Posz n) => Posz (Nat.lxor m n)
    | (Posz m), (Negz n) => Negz (Nat.lxor m n)
    | (Negz m), (Posz n) => Negz (Nat.lxor m n)
    | (Negz m), (Negz n) => Posz (Nat.lxor m n)
    end.
  
  Definition ldiff (x y : int) : int :=
    match x, y with
    | (Posz m), (Posz n) => Posz (Nat.ldiff m n) (* x & ~ y *)
    | (Posz m), (Negz n) => Posz (Nat.land m n)  (* x & ~ ~y = x & y *)
    | (Negz m), (Posz n) => Negz (Nat.lor m n)   (* ~x & ~ y = ~(x | y) *)
    | (Negz m), (Negz n) => Posz (Nat.ldiff n m) (* ~x & ~ ~y = ~ x & y *)
    end.
  
(**
testbit 関数を次のように定義できる。これは定義！
*)
(*
  Equations testbit (x : int) (m : nat) : bool :=
    testbit (Posz n) m := Nat.testbit n m ;
    testbit (Negz n) m := ~~ Nat.testbit n m.
  (* simp testbit で以下のrewrite ができる。 *)
  Check testbit_equation_1: forall n m : nat, testbit n m = Nat.testbit n m.
  Check testbit_equation_2: forall n m : nat, testbit (Negz n) m = ~~ Nat.testbit n m.
*)
  Definition testbit (x : int) (m : nat) : bool :=
    match x with
    | Posz n => Nat.testbit n m
    | Negz n => ~~ Nat.testbit n m
    end.

  Notation ".~ x" := (lnot x) (at level 35).
  Notation "x .& y" := (land x y) (at level 50).
  Notation "x .| y" := (lor x y) (at level 50).
  Notation "x .^ y" := (lxor x y) (at level 50).
  Notation "x .[ i ]" := (testbit x i).
  Notation "a ^^ b" := (xorb a b) (at level 50).
  
  Lemma lnot_spec (x : int) (i : nat) : (.~ x).[i] = ~~ x.[i].
  Proof.
    case: x => n //=.
    by rewrite negbK.
  Qed.
  
  Lemma lor_spec (x y : int) (i : nat) : (x .| y).[i] = x.[i] || y.[i].
  Proof.
    case: x; case: y;
      rewrite /testbit //= => x y;
        rewrite ?Nat.lor_spec ?Nat.land_spec ?Nat.ldiff_spec //=.
    - by rewrite negb_and negbK orbC.
    - by rewrite negb_and negbK orbC.
    - by rewrite negb_and.
  Qed.
  
  (* この証明から 2025/8/23 ProorCafe *)
  Lemma land_spec (x y : int) (i : nat) : (x .& y).[i] = x.[i] && y.[i].
  Proof.
    case: x; case: y;
      rewrite /testbit //= => x y;
        rewrite ?Nat.lor_spec ?Nat.land_spec ?Nat.ldiff_spec //=.
    - by rewrite andbC.
    - by rewrite negb_or.
  Qed.
  
  Lemma lxor_spec (x y : int) (i : nat) : (x .^ y).[i] = x.[i] ^^ y.[i].
  Proof.
    case: x; case: y;
      rewrite /testbit //= => x y;
        rewrite ?Nat.lxor_spec //=.
    - by rewrite Bool.negb_xorb_r.
    - by rewrite Bool.negb_xorb_l.
    - by rewrite Bool.xorb_negb_negb.
  Qed.
  
  Lemma ldiff_spec (x y : int) (i : nat) : (ldiff x y).[i] = x.[i] && ~~ y.[i].
  Proof.
    case: x; case: y;
      rewrite /testbit //= => x y;
        rewrite ?Nat.land_spec ?Nat.lor_spec ?Nat.ldiff_spec //=.
    - by rewrite negbK.
    - by rewrite negb_or.
    - by rewrite negbK andbC.
  Qed.
  
(**
# 数学ガールの問題を 自然数 (PeanoNat) の問題にする
 *)

  Definition p (x : int) := x .& (- x).

  Lemma p_diff n  : p (Posz n.+1) = Nat.ldiff n.+1 n.
  Proof.
    done.
  Qed.
  
  Lemma p_diff' n  : (0 < n)%N -> p (Posz n) = Nat.ldiff n n.-1.
  Proof.
    by case: n.
  Qed.
  
  Lemma p_0 i : (p 0).[i] = false.
  Proof.
    rewrite /p land_spec //=.
    by rewrite Nat.bits_0.
  Qed.
  
  Lemma p_pos n i : (p (Posz n.+1)).[i] = Nat.testbit n.+1 i && ~~ Nat.testbit n i.
  Proof.
    by rewrite land_spec.
  Qed.

  Lemma p_neg n i : (p (Negz n)).[i] = ~~ Nat.testbit n i && Nat.testbit n.+1 i.
  Proof.
    by rewrite land_spec.
  Qed.
  
(**
## 頑張った別の形式化
*)
  Definition p' (n : nat) := n .& (- n%:Z).
  
  (* a の n ビット目と、a/2 の n-1 ビット目は同じ。これは任意の自然数aで成り立つ。 *)
  Check Nat.testbit_div2
    : forall a n : nat, Nat.testbit (Nat.div2 a) n = Nat.testbit a n.+1.

  Lemma nat_ind2 :
    forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P (S (S n))) ->
      forall n : nat, P n.
  Proof.
    move=> P HP0 HP1 IH n.
    have H : (P n /\ P (S n)).
    - elim: n.
      + by split.
      + move=> n [] HPn HPsn.
        split=> //=.
        by apply: IH.
    - by case: H.
  Qed.
  
  Lemma coq_divn2 n : Nat.div2 n = n./2.
  Proof.
    elim/nat_ind2 : n => //= n IHn.
    by rewrite IHn.
  Qed.
  
  Lemma coq_evenP n : Nat.Even n <-> ~~ odd n.
  Proof.
    split => [/Nat.even_spec | H].
    - elim/nat_ind2 : n => [|| n IHn] //=.
      by rewrite negbK.
    - apply/Nat.even_spec.       
      elim/nat_ind2 : n H => [_ || n IHn] //=.
      by rewrite negbK.
  Qed.
  
  (* p 関数の引数が偶数の場合、testbit_div2 が使えそうである。 *)
  Lemma p_even (n i : nat) : (0 < n)%N -> ~~ odd n -> (p' n).[i.+1] = (p' n./2).[i].
  Proof.
    move=> Hn0 Hne.
    rewrite /p' 2!land_spec.
    f_equal.                                (* &　の左右で分ける。 *)
    
    (* 正の項（&の左）は、testbit_div2 がそのまま使える。 *)
    - rewrite /testbit -coq_divn2.
      by apply: Nat.testbit_div2.
      
    (* 負の項（&の右）は、``(n + 1) / 2 = n / 2`` に持ち込む。 *)
    - move: Hn0 Hne.
      case: n; case; try done.
      move=> n Hn0 Hne.
      have -> : n.+2./2 = n./2.+1 by lia.
      rewrite -[n.+2]addn1 /=.
      congr (~~ Nat.testbit _ i).
      
      Check Nat.Even_div2
        : forall n : nat, Nat.Even n -> Nat.div2 n = Nat.div2 n.+1.
      
      rewrite Nat.add_1_r -Nat.Even_div2.
      * by rewrite coq_divn2.
      * rewrite /= negbK in Hne.
        by apply/coq_evenP.
  Qed.
  
  Lemma mul2K n : n.*2./2 = n.
  Proof.
    lia.
  Qed.

  (* 似た様な補題 *)
  Lemma p_even' (n i : nat) : (0 < n)%N -> (p' n.*2).[i.+1] = (p' n).[i].
  Proof.
    move=> Hn0.
    rewrite (@p_even n.*2 i); try lia.
    by rewrite mul2K.
  Qed.
  
  (* 補題：偶数+1 diff 偶数 = 1 *)
  Lemma ldiff_even_n_n1_diff_n__1 n : ~~ odd n -> Nat.ldiff n.+1 n = 1.
  Proof.
    move/even_halfK => <-.
    rewrite -muln2 mulnC -addn1.
    
    Check Nat.ldiff_odd_even n n
      : Nat.ldiff ((2 * n)%coq_nat + 1)%coq_nat (2 * n)%coq_nat = ((2 * Nat.ldiff n n)%coq_nat + 1)%coq_nat.
    
    rewrite Nat.ldiff_odd_even Nat.ldiff_diag.
    rewrite Nat.mul_0_r Nat.add_0_l.
    done.
  Qed.
  
  (* p 関数の引数が奇数の場合、値は1なので、0ビットめだけtrue *)
  Lemma p_odd_bit0 (n : nat) : odd n -> (p' n).[0] = true.
  Proof.
    (* Check andb_true_intro. *)
    case: n => //= n Hno.
    by rewrite ldiff_even_n_n1_diff_n__1.
  Qed.
  
  (* p 関数の引数が奇数の場合、値は1なので、0ビットめ以外はfalse *)
  Lemma p_odd_not_bit0 (n : nat) (i : nat) : odd n -> (0 < i)%N -> (p' n).[i] = false.
  Proof.
    case: n => //= n Hno.
    rewrite ldiff_even_n_n1_diff_n__1 //.
    move/prednK => <-.
    rewrite -addn1.
    
    Check Nat.shiftr_spec 1 1
      : forall m : nat, Nat.le 0 m -> Nat.testbit (Nat.shiftr 1 1) m = Nat.testbit 1 (m + 1)%coq_nat.
  
    rewrite -( Nat.shiftr_spec 1 1) /=.
    - by rewrite Nat.bits_0.
    - lia.
  Qed.

(**
# ルーラー関数 の漸化式
*)
  
(**
以下の三つの定義が等しいことを証明したい。
*)
  Equations log2 (x : int) : nat :=
    log2 (Posz n) := Nat.log2 n;
    log2 (Negz _) := 0.
  Compute log2 0%Z.                         (* = 0%N *)
  
  Definition ruler (n : nat) := log2 (p' n). (* log2 (n%:Z .& (- n%:Z)) *)
  
  Definition ruler' (n : nat) := log2 (n%:Z .^ n.-1%:Z).
  
  Equations ruler_rec (n : nat) : nat by wf n :=
    ruler_rec 0 => 0 ;
    ruler_rec n.+1 with odd n.+1 => {
      | true  => 0 ;
      | false => (ruler_rec n.+1./2).+1
      }.
  Obligation 1.
  apply/ltP.
  rewrite ltn_uphalf_double -muln2.
  by apply: ltn_Pmulr.
  Qed.

  Example test (n : nat) := (ruler n = ruler_rec n).
  Example test' (n : nat) := (ruler' n = ruler_rec n).
  Example test2 (n : nat) := (ruler n = ruler' n).

  Goal test 0. Proof. done. Qed.
  Goal test 1. Proof. done. Qed.
  Goal test 2. Proof. done. Qed.
  Goal test 3. Proof. done. Qed.
  Goal test 4. Proof. done. Qed.
  Goal test 5. Proof. done. Qed.
  Goal test 6. Proof. done. Qed.
  Goal test 7. Proof. done. Qed.
  Goal test 8. Proof. done. Qed.
  
  Compute ruler 0.
  Compute ruler 1.
  Compute ruler 2.
  Compute ruler 3.
  Compute ruler 4.
  Compute ruler 5.  
  Compute ruler 7.  
  Compute ruler 8.  
  
  Compute ruler_rec 0.
  Compute ruler_rec 1.
  Compute ruler_rec 2.
  Compute ruler_rec 3.
  Compute ruler_rec 4.
  Compute ruler_rec 5.  
  Compute ruler_rec 7.  
  Compute ruler_rec 8.  

(**
## ruler_rec の定義から明らかな性質
*)
  Lemma ruler_rec_0 : ruler_rec 0 = 0.
  Proof.
    by simp ruler_rec.
  Qed.

  Lemma ruler_rec_odd (n : nat) : odd n -> ruler_rec n = 0.
  Proof.
    case: n => //= n Ho.
    simp ruler_rec.
    rewrite [odd n.+1]/= Ho.
    by rewrite ruler_rec_clause_2_equation_1.
  Qed.

  Lemma ruler_rec_even (n : nat) : (0 < n)%N -> ~~ odd n -> ruler_rec n = (ruler_rec n./2).+1.
  Proof.
    case: n => //= n Hn.
    rewrite negbK => He.
    simp ruler_rec => //=.
    rewrite He.
    rewrite ruler_rec_clause_2_equation_2 /=.
    done.
  Qed.
  
End bitwise.
  
  (**
別の定義：

x = n (> 0) のとき、n と n.-1 を一致するまで、右シフトまたは2で割るを繰り返す。
繰り返しの回数が m なら、ルーラー関数の値は m.-1

x = 6
6 3 1
5 2 1
2回しふとなので、値は1

x=3
3 1
2 1
1回しふとなので、値は0

x=4
4 2 1 0
3 1 0 0
3回しふとなので、値は2


x=8
8 4 2 1 0
7 3 1 0 0
4回しふとなので、値は3
*)

(**
# 補足説明

## Standard Coq

- NArith/BinNatDef.v
- ZArith/BinInt.v       ZArith/Zbitwise.v


## Lean

- Mathlib/Data/Num/Bitwise.lean
- Mathlib/Data/Int/Bitwise.lean

Negz にあたるコンストラクタは neg_succ_of_nat という

``-[ ・ +1]`` または ``-[1+ ・ ]`` というノーテーション

*)

(* END *)
