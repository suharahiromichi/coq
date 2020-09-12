(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.3 ssrnat.v --- n == 0 に関連する補題

======

2020_06_23 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 自然数 n が 0 に等しい

自然数 n が 0 に等しい、または、等しくないことについての証明は、
頻出するので、まとめてみます。
*)

Section LE0.
(**
## つねに成立する命題
*)
  Check leq0n : forall n : nat, 0 <= n.
  Check ltn0Sn : forall n : nat, 0 < n.+1.

(**
## 成立しない命題
 *)
  Check ltn0 : forall n : nat, (n < 0) = false.

(**
## 同値の関係の命題
*)
  (**
     "<" は leq ("<=") の表記(Notation、構文糖)であるため、
     "<=" も "<" を使って表示される。
     Coq はできるだけ、表記を使おうとするため (pretty-print) 。
   *)
  Locate "_ < _".                           (* leq m.+1 n *)
  
  (* 1 <= n と 0 < n とは表記として、同じ。 *)
  Goal forall n, (1 <= n) = (0 < n).
  Proof.
    move=> n.
    (* (0 < n) = (0 < n) *)
    done.
  Qed.
  
  (* n <= 0 と n < 1 とは表記(Notation)としては、異なる。 *)
  Goal forall n, (n <= 0) = (n < 1).
  Proof.
    move=> n.
    (* (n <= 0) = (n.+1 <= 1) *)
    rewrite /leq.
    (* ((n - 0) == 0) = ((n.+1 - 1) == 0) *)
    done.
  Qed.
  
  Check lt0n : forall n : nat, (0 < n) = (n != 0).
  Goal forall n : nat, (1 <= n) = (n != 0).
  Proof. apply: lt0n. Qed.
  
  Check leqn0 : forall n : nat, (n <= 0) = (n == 0).
  Goal forall n : nat, (n < 1) = (n == 0).
  Proof. apply: leqn0. Qed.
  
  (* このあたりは、boolの式の問題 *)
  (* https://qiita.com/suharahiromichi/items/85773d5af998ae3fe148 *)
  Check eqn0Ngt : forall n : nat_eqType, (n == 0) = ~~ (0 < n).
  Check neq0_lt0n : forall n : nat_eqType, (n == 0) = false -> 0 < n.
  
(**
## その他
*)
  Check lt0n_neq0 : forall n : nat, 0 < n -> n != 0.


(**
# 自然数 n が n に等しい
*)

(**
## つねに成立する命題
*)
  Check leqnn : forall n : nat, n <= n.
  Check ltnSn : forall n : nat, n < n.+1.
  Check leq_pred : forall n : nat, n.-1 <= n.
  Check leqSpred : forall n : nat, n <= n.-1.+1.
  
  Check prednK : forall n : nat, 0 < n -> n.-1.+1 = n. (* 注意！条件あり *)

(**
## 成立しない命題
 *)
  Check ltnn : forall n : nat, (n < n) = false.
  
(**
## n - n = 0

案外とこの補題が用意されていない。
 *)
  Lemma le_subn m n : m <= n -> m - n = 0.
  Proof. move=> H. apply/eqP. by rewrite subn_eq0. Qed.
  
  Lemma eq_subn n : n - n = 0.
  Proof. apply/eqP. by rewrite subn_eq0. Qed.
  
(**
補題を用意するのが面倒なので、have で前提に用意してもよい。
*)
  Goal forall m n, iota m (n - n) = [::].
  Proof.
    move=> m n.
    have -> : n - n = 0 by apply/eqP; rewrite subn_eq0.
    (* have -> : n - n = 0 by ssroega. *)
    done.
  Qed.

(**
## その他
 *)
  Check eq_leq : forall m n : nat, m = n -> m <= n.

(**
論理バズルで取り上げられる（有名？）な補題だが、
Coq の場合、証明図を下から上に積み上げていくので、結論を前提に置き換えていくので、
なにも考えずに、手当たり次第に apply していくと、
 *)  
  Goal 2 <= 3.
  Proof.
    apply: eq_leq.                          (* 2 = 3 *)
  (**
     Coqの証明が行き詰まることの多くは、大抵こんなことが原因である。
   *)
  Admitted.
    
End LE0.

(**
# ltnS のトリック

これは Notation に関する、ただの等式なのである。
 *)
Section LtnS.
  Variable m n : nat.
  
  Check ltnS m n : (m <= n) = (m <= n).
  Check ltnS m n : (m <= n) = (m < n.+1).
  Check ltnS m n : (m <= n) = (m.+1 <= n.+1).
  Check ltnS m n : (m <= n) = (m.+1 < n.+2).
  
  Check ltnS m.+1 n : (m < n) = (m < n).
  Check ltnS m.+1 n : (m < n) = (m.+1 <= n).
  Check ltnS m.+1 n : (m < n) = (m.+1 < n.+1).
  Check ltnS m.+1 n : (m < n) = (m.+2 <= n.+1).
End LtnS.

(**
一般の m と n の関係については省略しています。
*)

Section これだけは.
  (* ssomega で解ける場合もあるが、手で解いておく。 *)
  
  (* 2より大きいなら、1より大きい。  *)
  Lemma le1_le m x : m.+1 <= x -> m <= x.
  Proof.
    move=> H.
      by rewrite ltnW.
  Qed.
  Check @le1_le 1 : forall x : nat, 2 <= x -> 1 <= x.
  
  Lemma lem_len m n x : m <= n -> n <= x -> m <= x.
  Proof.
    move=> Hmn H.
      by apply: (@leq_trans n m).
  Qed.
  Check @lem_len 1 2 : forall x : nat, 1 <= 2 -> 2 <= x -> 1 <= x.
  
  (* n <= m の反対は m < n だが、m <= n で証明したい。 *)
  Lemma le_m_n m n : (n <= m) = false -> m <= n.
  Proof.
    move/negbT => Hmn.
    rewrite -ltnNge in Hmn.
      by rewrite ltnW //.
  Qed.

End これだけは.

(* END *)
