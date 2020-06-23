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
  Check leqn0 : forall n : nat, (n <= 0) = (n == 0).
  Goal forall n : nat, (n < 1) = (n == 0).
  Proof. apply: leqn0. Qed.

  Check lt0n : forall n : nat, (0 < n) = (n != 0).
  Goal forall n : nat, (1 <= n) = (n != 0).
  Proof. apply: lt0n. Qed.
  
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
# その他
 *)
  Check eq_leq : forall m n : nat, m = n -> m <= n.

End LE0.

(**
一般の m と n の関係については省略しています。
*)

(* END *)
