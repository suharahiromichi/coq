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

5. Type Progress ... 型の進行性。型のついた項の正規形は値である。（ステップが行き詰まらない）

6. Type Preservation ... 型の保存性。型のついた項をステップしても、また型のつく項である。

7. Type Soundness ... 型の安全性（健全性ともいう） TAPL日本語版 p.72。
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

Locate "_ ==> _".                           (** ["t1 '==>' t2" := step t1 t2] *)
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
  | ST_IszeroZero : tiszero tzero ==> ttrueo
  | ST_IszeroSucc : forall t1 : tm, nvalue t1 -> tiszero (tsucc t1) ==> tfalse
  | ST_Iszero : forall t1 t1' : tm, t1 ==> t1' -> tiszero t1 ==> tiszero t1'.
]]
*)

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
(** とりあえず、以降では使わない。  *)

(* ================================================================= *)
(** ** Typing *)

Print ty.
(**
[[
Inductive ty : Set :=
 | TBool : ty
 | TNat : ty.
]]
*)

Locate "|- _ \in _".                        (** [has_type t T] *)
Print has_type.
(**
[[
Inductive has_type : tm -> ty -> Prop :=
  | T_True : |- ttrue \in TBool
  | T_False : |- tfalse \in TBool
  | T_If : forall (t1 t2 t3 : tm) (T : ty),
           |- t1 \in TBool ->
           |- t2 \in T -> |- t3 \in T -> |- tif t1 t2 t3 \in T
  | T_Zero : |- tzero \in TNat
  | T_Succ : forall t1 : tm, |- t1 \in TNat -> |- tsucc t1 \in TNat
  | T_Pred : forall t1 : tm, |- t1 \in TNat -> |- tpred t1 \in TNat
  | T_Iszero : forall t1 : tm, |- t1 \in TNat -> |- tiszero t1 \in TBool.
]]
 *)

Check has_type_1 : |- tif tfalse tzero (tsucc tzero) \in TNat. (** 型が付く *)
Check has_type_not : ~ (|- tif tfalse tzero ttrue \in TBool).  (** 型が付かない *)

(* suhara *)
(** 項の型を返す関数。計算量がO(n)であること。  *)
Fixpoint type_of (t : tm) : option ty :=
  match t with
  | ttrue => Some TBool
  | tfalse => Some TBool
  | tif t1 t2 t3 => match type_of t1 with
                    | Some TBool => match type_of t2 with
                                    | Some TBool => match type_of t3 with
                                                    | Some TBool => Some TBool
                                                    | _ => None
                                                    end
                                    | Some TNat  => match type_of t3 with
                                                    | Some TNat  => Some TNat
                                                    | _ => None
                                                    end
                                    | _ => None
                                    end
                    | _ => None
                    end
  | tzero => Some TNat
  | tsucc t1 => match type_of t1 with
                | Some TNat => Some TNat
                | _ => None
                end
  | tpred t1 => match type_of t1 with
                | Some TNat => Some TNat
                | _ => None
                end
  | tiszero t1 => match type_of t1 with
                  | Some TNat => Some TBool
                  | _ => None
                  end
  end.

Compute type_of (tif tfalse tzero (tsucc tzero)). (** Some TNat *)
Compute type_of (tif tfalse tzero ttrue).         (** None *)

Lemma equiv_types_1 t ty : type_of t = Some ty -> |- t \in ty.
Proof.
  intros H.
  generalize dependent ty.
  induction t; intros ty H; inversion H.
  - easy.
  - easy.
  - apply T_If.
    + apply IHt1.
      destruct (type_of t1).
      * now destruct t.
      * easy.
    + apply IHt2.
      destruct (type_of t1).
      * destruct (type_of t2).
        ** destruct (type_of t3).
           *** destruct t.
               **** destruct t0.
                    ***** now destruct t4.
                    ***** now destruct t4.
               **** now destruct t0.
           *** destruct t.
               **** now destruct t0.
               **** now destruct t0.
        ** now destruct t.
      * easy.
    + apply IHt3.
      destruct (type_of t1).
      * destruct (type_of t2).
        ** destruct (type_of t3).
           *** destruct t.
               **** destruct t0.
                    ***** now destruct t4.
                    ***** now destruct t4.
               **** now destruct t0.
           *** destruct t.
               **** now destruct t0.
               **** now destruct t0.
        ** now destruct t.
      * easy.
  - easy.
  - destruct ty.
    + destruct (type_of t).
      * now destruct t0.
      * easy.
    + apply T_Succ.
      apply IHt.
      destruct (type_of t).
      * now destruct t0.
      * easy.
  - destruct ty.
    + destruct (type_of t).
      * now destruct t0.
      * easy.
    + apply T_Pred.
      apply IHt.
      destruct (type_of t).
      * now destruct t0.
      * easy.
  - destruct ty.
    * apply T_Iszero.
      destruct (type_of t).
      ** destruct t0.
         *** easy.
         *** now apply IHt.
      ** easy.
    * destruct (type_of t).
      ** now destruct t0.
      ** easy.
Qed.

Lemma equiv_types_2 t ty : |- t \in ty -> type_of t = Some ty.
Proof.
  intros H.
  induction H.
  - easy.
  - easy.
  - inversion t1; simpl;
      rewrite IHhas_type1; simpl;
        rewrite IHhas_type2; simpl;
          rewrite IHhas_type3; simpl;
            now destruct T.
  - easy.
  - inversion t1; simpl;
      now rewrite IHhas_type.
  - inversion t1; simpl;
      now rewrite IHhas_type.
  - inversion t1; simpl;
      now rewrite IHhas_type.
Qed.

Theorem equiv_types t ty : type_of t = Some ty <-> |- t \in ty.
Proof.
  split.
  - apply equiv_types_1.
  - apply equiv_types_2.
Qed.


(** 正準形  *)
(** 項の型がBoolで、項が値なら、その項はBool値である。 *)
Check bool_canonical : forall t, |- t \in TBool -> value t -> bvalue t.
(** 項の型がNatで、項が値なら、その項はNat値である。 *)
Check nat_canonical : forall t, |- t \in TNat -> value t -> nvalue t.

(* ================================================================= *)
(** ** Progress *)
(** 項tが型Tなら、tは値かステップできる。 *)
Check progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.

(* ================================================================= *)
(** ** Type Preservation *)
(** 項tが型Tで、tがt'にステップできるなら、t'の型はTである。 *)
Check preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

(* ================================================================= *)
(** ** Type Soundness *)
(** 項tが型Tで、tがt'にマルチステップできるなら、t'は行き詰まっていない。
        つまり、tはマルチステップして値になる。 *)
Check soundness : forall t t' T,
  |- t \in T ->
  t ==>* t' ->
  ~(stuck t').

(* END *)
