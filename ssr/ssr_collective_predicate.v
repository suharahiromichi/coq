From mathcomp Require Import all_ssreflect.

(** ssrbool.v を参照のこと！ *)

(* Set Printing All. *)

(** # pred *)

(** pred = T -> bool *)
Compute pred nat.                           (* nat -> bool *)


(** # simpl_pred *)

Check SimplPred nat_eqType : simpl_pred nat.

(** 自動で簡約される。 *)
Goal SimplPred nat_eqType 1.
Proof. move=> /=. done. Qed.

(** mem_pred は 中置記法を保存する simpl_pred の亜種である。  *)
Check mem nat_eqType       : mem_pred nat.

(** 1 \in nat に簡約される。 *)
Goal mem nat_eqType 1.
Proof. move=> /=. done. Qed.

(** x \in A は自動で簡約されない。明示的に apply inE または rewrite inE で簡約する。 *)
Goal 1 \in nat_eqType.
Proof. by rewrite inE. Qed.


(** # Applicative Predicate と Collective Predicate *)
(** 前置記法 P x か、中置記法 x \in A の違いだが、 =1 と =i の違いでもある。 *)

(** ## Applicative Predicate *)
(** [pred x | nat_eqType x] x = [pred x | nat_eqType x] x *)
Goal [pred x | nat_eqType x] =1 [pred x | nat_eqType x].
Proof. move => x. done. Qed.

(** ## Collective Predicate *)
(** (x \in mem nat_eqType) = (x \in mem nat_eqType) *)
Goal mem nat_eqType =i mem nat_eqType.
Proof. move=> x. done. Qed.


(** # Collective Predicate を定義する。 *)

(** ## predType のインスタンスとして、Collective Predicate を定義してみる。 *)

Fail Check mem (0,1) : mem_pred nat_eqType.
Fail Check mem (0,1) 1.
Fail Check (0,1) 1.
Fail Check 1 \in (0,1).
Fail Check (0,1) =i (0,1).

Section Pair.
  Variable T : eqType.
(*
  Coercion pred_of_eq_pair (s : T * T) : pred_class :=
    fun (x : T) =>  (s.1 == x) || (s.2 == x).
*)
  Coercion pred_of_eq_pair (s : T * T) : pred_class :=
    xpredU (eq_op s.1) (eq_op s.2).
  
  Canonical pair_predType := @mkPredType T (T * T) pred_of_eq_pair.
  Canonical mem_pair_predType := mkPredType pred_of_eq_pair.
  Check pair_predType : predType T.
End Pair.
Check pair_predType : forall T : Equality.type, predType (Equality.sort T).
Check pair_predType nat_eqType : predType nat.

Check mem (0,1) : mem_pred nat_eqType.
Check mem (0,1) 1.
Fail Check (0,1) 1.                         (* これはだめ。 *)
Check 1 \in (0,1).
Check (0,1) =i (0,1).


(** ## predArgType を使って、Collective Predicate を定義してみる。 *)
(** total predicate ある型の要素についてすべてtrueを返す関数。これを母関数として持つ。 *)
Check fun _ => true.

(** ### 比較 Type で定義したもの。 *)
Inductive news' : Type := n' | e' | w' | s'.

Fail Check mem news' : mem_pred news'.
Fail Check mem news' n'.
Fail Check n' \in news'.
Fail Check mem news'.
Fail Check news' =i news'.

(** ### {: T} を使えば、predArgType に cast できる。  *)
Check mem {: news'} : mem_pred news'.
Check mem {: news'} n'.
Check n' \in {: news'}.
Check mem {: news'}.
Check {: news'} =i {: news'}.


(** ### predArgType で定義したもの。 *)
Inductive news : predArgType := n | e | w | s.

Check mem news : mem_pred news.
Check mem news n.
Check news n.
Check n \in news.
Check news =i news.


(** ### 任意の型を Type から predType に変換する。 *)
Check {: news'} : predArgType.
Check {: nat} : predArgType.


(** # Collective Predicate の演算 *)

Compute 1 \in [predU (0,1) & (0,2)].        (* union *)
Compute 1 \in [predI (0,1) & (0,2)].        (* intersection *)
Compute 1 \in [predD (0,1) & (0,2)].        (* difference *)



(** # おまけ *)

Check [pred x | nat_eqType x] : simpl_pred nat.


(* **************************** *)
(* **************************** *)
(* **************************** *)

Check 1 == 1.

Definition P (x : nat) := x == 1.

Check SimplPred P : simpl_pred nat.

Check SimplPred P.
Check predType nat.

Variable m : nat.

Check nat_eqType : pred nat.
Check {: nat} : pred nat.
Check mem [:: 1] : mem_pred nat.

Goal SimplPred P 1.
  simpl.
Admitted.

Goal 1 \in [predI [::1] & [::1]].
  simpl.
Admitted.

Goal m \in [pred x | nat_eqType x].
  simpl.
Admitted.

Goal SimplPred nat_eqType m.
  simpl.
Admitted.

Goal mem nat_eqType m.
  simpl.
Admitted.

Goal mem {: nat} 1.
  simpl.
Admitted.

Check nat_eqType : pred nat.
Check nat_eqType : simpl_pred nat.

Check SimplPred nat_eqType : pred nat.
Check SimplPred nat_eqType : simpl_pred nat.

Check mem nat_eqType : pred nat.
Check mem nat_eqType : simpl_pred nat.
Check mem nat_eqType : mem_pred nat.

  
Goal SimplPred {: nat} 1.
  simpl.
  Admitted.

Check nat_eqType  =1 nat_eqType.

Check {: nat} =1 {: nat}.
Check {: nat} =i {: nat}.

Fail Check [:: 1] =1 [:: 1].
Check [:: 1] =i [:: 1].
  
Check mem P.
Goal mem P m.
  simpl.
Admitted.

About mem_pred.
Print mem_pred.

Check PredType.
Check 1 \in nat_eqType.

Goal nat_eqType 1 .
  simpl.
Admitted.
  
Goal mem nat_eqType 1 .
  simpl.
  simpl.
Admitted.

Check mem nat_eqType 1.
Check nat_eqType 1.
Check true \in {: bool}.
Check {: bool} true.

Set Printing All.
Check 1 \in nat_eqType.
Check mem nat_eqType 1.

(* END *)
