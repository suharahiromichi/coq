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
(** ProofCafe ##76 2018/06/16 *)

(** 概要

1. Syntax ... 前章より複雑な項を定義する。
ここで定義するものは、TAPLの第8章で定義するものと同じ。

2. Operational Semantics ... Syntaxを定義した項についてステップ（==>）を定義する。
(single-step) small-step 評価関係(簡約関係)。

3. Normal Forms and Values ... 強正規化が成り立たない。
すなわち、値ではないが、もうステップできない項があることを示す。
（もうこれ以上簡約できない、行き詰まる、スタックstuckする、項がある。(tsucc ttrue)）
では、どんな項だと行き詰まるのか。それを事前に知ることはできないだろうか。

4. Typing ... 型を導入する。正しく型付けされている(well-typed)項という。

(おまけ。型付は決定的であること。型を返す手続きを定義してみる。O(n)であること）

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
  | ST_IszeroZero : tiszero tzero ==> ttrue
  | ST_IszeroSucc : forall t1 : tm, nvalue t1 -> tiszero (tsucc t1) ==> tfalse
  | ST_Iszero : forall t1 t1' : tm, t1 ==> t1' -> tiszero t1 ==> tiszero t1'.
]]
*)

(**
Hint Constructors step.
*)

(* ================================================================= *)
(** ** Normal Forms and Values *)

(** 前章 Smallstep.v の復習：
（定義）項が正規形であるとは、その項がもうこれ以上ステップできないことをいう。
normal_form
この定義は、本章 Types.v でも引き継ぐ。

（定理）項が正規形であることと、項が値であることは同値である。
nf_same_as_value

この定理は、nf_is_value と value_is_nf からなる。
本章の項の定義では nf_is_value が成立しないので、同値ではない。
 *)

(** 正規形 normal_form の定義は前章の定義を使う。
もうステップできない項の意味である。 *)
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

(**
（定義）正規形だが値でない項を、ステップが行き詰まる(stuck)項と呼ぶ。
（定理）本章の項の定義だと、ステップが行き詰まる項がある。
*)
Check stuck : tm -> Prop.
Print stuck.
(**
[[
stuck = fun t : tm => step_normal_form t /\ ~ value t.
]]
 *)

(** ステップが行き詰まる項が存在することを証明する。 *)
(** 前章の [nf_is_value : forall t, normal_form step t -> value t] と比べる。  *)
Check some_term_is_stuck : exists t : tm, stuck t.
Check some_term_is_stuck : exists t : tm, normal_form step t /\ ~ value t.

(* suhara *)
(** ns_is_value の否定を証明する。 *)
Goal ~ (forall t, normal_form step t -> value t).
Proof.
  intro Hc.
  Check Hc (tsucc ttrue).              (* 具体的に、行き詰まる項 (tsucc ttrue) を与える。 *)
  destruct (Hc (tsucc ttrue)).         (* それについて、ns_is_value の否定を証明する。 *)
  - unfold step_normal_form.
    intro H.
    destruct H.
    now inversion H.
  - now inversion H.
  - now inversion H.
Qed.

(**
問題提起：どんな項だと行き詰まるのか、行き詰まらないのか。
それを事前に知ることができるだろうか。

答えは、Type Progress の節を参照のこと。
 *)

(** 値は正規形である。値ならステップできない項である。 *)
(** これは、前章の結果とおなじ。  *)
Check value_is_nf : forall t : tm, value t -> normal_form step t.
Check value_is_nf : forall t : tm, value t -> step_normal_form t.
Check value_is_nf : forall t : tm, value t -> ~ (exists t', t ==> t').

(* suhara *)
Lemma value_is_not_step t1 t2 : value t1 -> ~ t1 ==> t2.
Proof.
  intros H Contra.
  apply value_is_nf in H.
  apply H.
  now exists t2.
Qed.

(**
（定理) ステップは決定的である。
 *)
(** 決定的であることの定義は前章の定義を使う。 *)
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
(** とりあえず、以降では使わない。  *)
Check step_deterministic : forall x y1 y2, x ==> y1 -> x ==> y2 -> y1 = y2.

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
(* オリジナルのテキストだと、正準形に飛ぶ。 *)

(* suhara *)
(** 型付けは決定的である。[TAPL 定理8.2.4] *)
(** とりあえず、以降では使わない。  *)
Theorem type_deterministic t ty1 ty2 :
    has_type t ty1 -> has_type t ty2 -> ty1 = ty2.
Proof.
  intros Hy1 Hy2.
  induction Hy1; inversion Hy2; subst; try easy.
  now apply IHHy1_2.
Qed.

(* suhara *)
(** 項の型を返す関数。計算量がO(n)であること。 *)
(** とりあえず、以降では使わない。  *)
Fixpoint type_of (t : tm) : option ty :=
  match t with
  | ttrue => Some TBool
  | tfalse => Some TBool
  | tif t1 t2 t3 => match type_of t1 with
                    | Some TBool => match (type_of t2, type_of t3) with
                                    | (Some TBool, Some TBool) => Some TBool
                                    | (Some TNat,  Some TNat)  => Some TNat
                                    | _                        => None
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

(** 型を返す関数が、型付けの結果と同じになるとを証明する。 *)
Lemma equiv_types_1 t ty : type_of t = Some ty -> |- t \in ty.
Proof.
  intros H.
  generalize dependent ty.
  induction t; intros ty H; inversion H.
  - easy.
  - easy.
  - apply T_If.
    + apply IHt1.
      now destruct (type_of t1) as [t |]; try destruct t.
    + apply IHt2.
      try destruct (type_of t1) as [t |];
        try destruct (type_of t2) as [t' |];
        try destruct (type_of t3) as [t'' |];
        try destruct t; try destruct t'; try destruct t'';
          easy.
    + apply IHt3.
      try destruct (type_of t1) as [t |];
        try destruct (type_of t2) as [t' |];
        try destruct (type_of t3) as [t'' |];
        try destruct t; try destruct t'; try destruct t'';
          easy.
  - easy.
  - destruct ty.
    + now destruct (type_of t) as [t' |]; try destruct t'.
    + apply T_Succ.
      apply IHt.
      now destruct (type_of t) as [t' |]; try destruct t'.
  - destruct ty.
    + now destruct (type_of t) as [t' |]; try destruct t'.
    + apply T_Pred.
      apply IHt.
      now destruct (type_of t) as [t' |]; try destruct t'.
  - destruct ty.
    + apply T_Iszero.
      apply IHt.
      now destruct (type_of t) as [t' |]; try destruct t'.
    + now destruct (type_of t) as [t' |]; try destruct t'.
Qed.

Lemma equiv_types_2 t ty : |- t \in ty -> type_of t = Some ty.
Proof.
  intros H.
  induction H as [| | t' | | t' | t' | t'].
  - easy.
  - easy.
  - inversion t'; simpl;
      rewrite IHhas_type1; simpl;
        rewrite IHhas_type2; simpl;
          rewrite IHhas_type3; simpl;
            now destruct T.
  - easy.
  - inversion t'; simpl;
      now rewrite IHhas_type.
  - inversion t'; simpl;
      now rewrite IHhas_type.
  - inversion t'; simpl;
      now rewrite IHhas_type.
Qed.

Theorem equiv_types t ty : type_of t = Some ty <-> |- t \in ty.
Proof.
  split.
  - now apply equiv_types_1.
  - now apply equiv_types_2.
Qed.
(** 項の型を返す関数。ここまで。suhara *)

(** 正準形、標準型 [TAPL 補題8.3.1] *)
(** Progress を証明するための補題である。  *)
(** 項の型がBoolで、項が値なら、その項はBool値である。 *)
Check bool_canonical : forall t, |- t \in TBool -> value t -> bvalue t.
(** 項の型がNatで、項が値なら、その項はNat値である。 *)
Check nat_canonical : forall t, |- t \in TNat -> value t -> nvalue t.

(* ================================================================= *)
(** ** Progress *)

(** 項tが型Tなら、tは値であるかステップできる。 *)
(** 進行 [TAPL 定理8.3.2] *)
Check progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.           (* ~ (stuck t) *)

(* ================================================================= *)
(** ** Type Preservation *)

(** 項tが型T かつ tがt'にステップできるなら、t'の型はTである。 *)
(** 保存 [TAPL 定理8.3.3] *)
Check preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

(* ================================================================= *)
(** ** Type Soundness *)

(** multi 反射推移閉包の定義は前章のを使う。 *)
Check @multi : forall X : Type, relation X -> relation X.
Print multi.
(**
[[
Inductive multi (X : Type) (R : relation X) : relation X :=
  | multi_refl : forall x : X, multi R x x
  | multi_step : forall x y z : X, R x y -> multi R y z -> multi R x z.
]]
*)

(** multistep マルチステップ簡約の定義は前章と同じである。
ただし、[Define multistep := (multi step).] と定義しなおす必要がある。 *)
Locate "_ ==>* _".                          (** [multistep t1 t2] *)
Check multistep.
Print multistep.                            (** [multi step] *)
Print multi.
(**
[[
  Inductive multi (X : Type) (R : relation X) : relation X :=
  | multi_refl : forall x : X, multi R x x
  | multi_step : forall x y z : X, R x y -> multi R y z -> multi R x z
]]
 *)

(** 項tが型Tで、tがt'にマルチステップできるなら、t'は行き詰まっていない。
        つまり、tはマルチステップして値になる。 *)
(** [健全性] *)

(** 進行性と保存性が証明されたことで、健全性が証明されたとしてもよいが、
ここでは、「型付けできる項は、マルチステップして値になる」
つまり、ステップを繰り返してもおかしくならない [TAPL] 、ということを証明する。
これを健全性、あるいは、安全性 と呼ぶ。
  *)

(** 証明：
まんなかの [t ==>* t'] で帰納法をする。

[mult_refl]のとき[x ==>* x]なので、[(|- x \in T) -> ~(stuck x)] を得る。
これは進行性を使って証明する。

[mult_step]のとき[x ==> y -> y ==>* z]なので、
[(|- x \in T) -> (x ==> y) -> (y ==>* z) -> ~(stuck z)] と、
帰納法の仮定 [(|- y \in T) -> ~(stuck z)] を得る。
帰納法の仮定をゴールに適用すると、[(|- x \in T) -> (x ==> y) -> (|- y \in T)] を得る。
これは保存性を使って証明する。
*)

(* suhara 証明を見直した。 *)
Corollary soundness : forall t t' T,
  |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P.
  
  Check multi_ind tm step.
  Check (fun t t' => |- t \in T -> ~(stuck t')).
  Check multi_ind tm step (fun t t' => |- t \in T -> ~(stuck t')) :
    (forall x : tm,
        |- x \in T -> ~(stuck x))
    ->
    (forall x y z : tm,
        x ==> y -> y ==>* z ->
        (|- y \in T -> ~(stuck z)) ->       (* IHP *)
        |- x \in T -> ~(stuck z))
    ->
    forall t t' : tm, t ==>* t' -> |- t \in T -> ~(stuck t').

  induction P.
  - intros [R S].                        (* ~(stuck x) を分解する。 *)
    now destruct (progress x T HT).
  - apply IHP.
    now apply (preservation x y T HT H).
Qed.

(* END *)
