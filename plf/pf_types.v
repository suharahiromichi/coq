(** ProofCafe SF/PLF Support Page *)
(** Types.v *)

(**
これは、「Software Foundations, Vol.2 Programming Language Foundations」 の
勉強会（ProofCafe）のサポートページです。復習などに利用しててください。

本ファイルの実行は、本ファイルを pfl ディレクトリの中に混ぜて置くか、
pfl のオリジナルの適当なファイルの適当な場所にcopy&pasteすることで可能です。
 *)

(** ご注意：

1. 実際の勉強会は、本ファイルではなく、オリジナルのファイルを直接編集・実行しておこないます。

2. 本ファイルには、演習問題の答えは含まれません。

*)

Require Import Coq.Arith.Arith.
Require Import Maps.
Require Import Imp. 
Require Import Smallstep.
Require Import Types.

(*
Hint Constructors multi.
 *)

(* ################################################################# *)
(** ProofCafe ##75 2018/03/21 *)

(** 概要

1. Syntax ... 前章より複雑な項を定義する。

2, Operational Semantics ... 前節で定義した項についてステップ（==>）を定義する。
(single-step) small-step 評価関係(簡約関係)。

3. Normal Forms and Values ... 強正規化が成り立たない。
すなわち、値ではないが、もうステップできない項があることを示す。
（もうこれ以上簡約できない、行き詰まる、スタックstuckする）

4. Typing ... 型を導入する。型のついた（well-typed) 項という。

5. Type Soundness ... 型の安全性（健全性ともいう） TAPL日本語版 p.72。

- 進行性 Progress ... 型のついた項の正規形は値である。（ステップが行き詰まらない）

- 型の保存性 Type Preservation ...型のついた項をステップしても、また型のつく項である。
 *)

(* ################################################################# *)
(** * Typed Arithmetic Expressions *)

(* ================================================================= *)
(** ** Syntax *)

Print tm.
(**
[[
Inductive tm : Set :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.
]]
 *)

Print bvalue.
(**
[[
Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.
]]
 *)

Print nvalue.
(**
[[
Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t : tm, nvalue t -> nvalue (tsucc t).
]]
*)

Check value : tm -> Prop.
Print value.
(**
[[
value = fun t : tm => bvalue t \/ nvalue t
     : tm -> Prop
]]
 *)
(*
Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.
 *)

(* ================================================================= *)
(** ** Operational Semantics *)

Print step.
(**
[[
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2 : tm, tif ttrue t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2 : tm, tif tfalse t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3 : tm,
            t1 ==> t1' -> tif t1 t2 t3 ==> tif t1' t2 t3
  | ST_Succ : forall t1 t1' : tm, t1 ==> t1' -> tsucc t1 ==> tsucc t1'
  | ST_PredZero : tpred tzero ==> tzero
  | ST_PredSucc : forall t1 : tm, nvalue t1 -> tpred (tsucc t1) ==> t1
  | ST_Pred : forall t1 t1' : tm, t1 ==> t1' -> tpred t1 ==> tpred t1'
  | ST_IszeroZero : tiszero tzero ==> ttrue
  | ST_IszeroSucc : forall t1 : tm, nvalue t1 -> tiszero (tsucc t1) ==> tfalse
  | ST_Iszero : forall t1 t1' : tm, t1 ==> t1' -> tiszero t1 ==> tiszero t1'.
]]
*)

Locate "_ ==> _".                           (** ["t1 '==>' t2" := step t1 t2] *)
(**
Hint Constructors step.
*)

(** 正規形 normal_form の定義は前章と同じく、もうステップできない項の意味である。 *)
Check @normal_form : forall X : Type, relation X -> X -> Prop.
Print normal_form.
(**
[[
normal_form = 
fun (X : Type) (R : relation X) (t : X) => ~ (exists t' : X, R t t')
     : forall X : Type, relation X -> X -> Prop
]]
*)
Print step_normal_form.                     (** [normal_form step] *)

Check stuck : tm -> Prop.
Print stuck.
(**
[[
stuck = fun t : tm => step_normal_form t /\ ~ value t.
]]
 *)

(** ステップが行き詰まる項が存在する。ステップできないが、値でもない項がある。 *)
Check some_term_is_stuck : exists t : tm, stuck t.
Check some_term_is_stuck : exists t : tm, normal_form step t /\ ~ value t.

(** 値は正規形である。値ならステップできない項である。 *)
Check value_is_nf : forall t : tm, value t -> step_normal_form t.
Check value_is_nf : forall t : tm, value t -> normal_form step t.

(* suhara *)
Lemma value_is_not_step t1 t2 : value t1 -> ~ t1 ==> t2.
Proof.
  intros H Contra.
  apply value_is_nf in H.
  apply H.
  now exists t2.
Qed.

(** 決定的であることの定義は前章と同じである。 *)
Check @deterministic : forall X : Type, relation X -> Prop.
Print deterministic.
(**
[[
deterministic = 
fun (X : Type) (R : relation X) =>
forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2
     : forall X : Type, relation X -> Prop
]]
 *)
(** ステップは決定的である。 *)
Check step_deterministic : forall x y1 y2, x ==> y1 -> x ==> y2 -> y1 = y2.


(* ================================================================= *)
(** ** Typing *)


(* END *)
