(** ProofCafe SF/PLF Support Page *)
(** StlcProp.v *)

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
Require Import Stlc.
Require Import StlcProp.

(* ################################################################# *)
(** ProofCafe ##82 2018/12/15 *)

(**
目次

*)

(**
概要

STLCについて、進行性と保存性を証明し、さらに安全性（健全性）を証明する。
定義および証明の流れは、Typesで定義した項と同じである。
*)

(** Typesで定義した項の場合 *)
(** TAPL 8.3、日本版 p.72 *)
Check progress : forall (t : tm) (T : ty),
    |- t \in T -> value t \/ (exists t' : tm, t ==> t').
Check preservation : forall (t t' : tm) (T : ty),
    |- t \in T -> t ==> t' -> |- t' \in T.
Check soundness : forall (t t' : tm) (T : ty),
    |- t \in T -> t ==>* t' -> ~ stuck t'.

Import STLC.
Import STLCProp.

(** STLC の場合 *)
(** TAPL 9.3、日本版 p.78 *)
Check progress : forall (t : tm) (T : ty),
    empty |- t \in T -> value t \/ (exists t' : tm, t ==> t').
Check preservation : forall (t t' : tm) (T : ty),
    empty |- t \in T -> t ==> t' -> empty |- t' \in T.
Check soundness : forall (t t' : tm) (T : ty),
    empty |- t \in T -> t ==>* t' -> ~ stuck t'.

(** 1. *)
(** 正準形、標準型 [TAPL 補題9.3.4] *)
(** 進行性 Progress を証明するための補題である。 *)
(** 項の型がBoolで、項が値なら、その項はtrueかfalse(Bool値)である。 *)
Check canonical_forms_bool :
  forall t : tm, empty |- t \in TBool -> value t -> t = ttrue \/ t = tfalse.
(** 項の型が関数抽象で、項が値なら、その項は適当な項uに対して λx.u である。 *)
Check canonical_forms_fun : forall (t : tm) (T1 T2 : ty),
    empty |- t \in TArrow T1 T2 ->
                      value t -> exists (x : id) (u : tm), t = tabs x T1 u.
(** 証明は、どちらも HVal : value t を destruct で場合分けする。 *)

(** 2. *)
(** 進行性 Progress [TAPL 定理9.3.5] *)
(** t が閉じた、正しく型付けされた項であるなら、Stackしない(行き詰まらない)。あるいは、
    t は値であるか、ステップすることができる。 *)

(** 値であるとは： *)
Check value : tm -> Prop.
Print value.
(*
Inductive value : tm -> Prop :=
    v_abs : forall (x : id) (T : ty) (t : tm), value (tabs x T t)
  | v_true : value ttrue
  | v_false : value tfalse
 *)

(** ステップできるとは： *)
Check step : tm -> tm -> Prop.       (* 2項がステップの関係である。 *)
Print step.
(*
Inductive step : tm -> tm -> Prop :=
    ST_AppAbs : forall (x : id) (T : ty) (t12 v2 : tm),
                value v2 -> tapp (tabs x T t12) v2 ==> [x := v2] t12
  | ST_App1 : forall t1 t1' t2 : tm, t1 ==> t1' -> tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2' : tm,
              value v1 -> t2 ==> t2' -> tapp v1 t2 ==> tapp v1 t2'
  | ST_IfTrue : forall t1 t2 : tm, tif ttrue t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2 : tm, tif tfalse t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3 : tm, t1 ==> t1' -> tif t1 t2 t3 ==> tif t1' t2 t3
 *)
Check forall t, exists t', step t t' : Prop. (* t がステップできる。 *)

(** 補足説明：t がステップできない場合、正規形 normal form と呼ぶ。
    正規形と値は異なるかもしれない。保存性の定理を参照のこと。 *)
Check forall t, normal_form step t : Prop.

(** 証明の概要：
    empty |- t \in T 、つまり has_type の定義による帰納法で証明する。
    - t が、変数であるとき、変数は空コンテキストから型付できないので矛盾である。
    - t が、True、False または 関数抽象 [λx:T'.t1] の場合は、値なので自明である。
    - t が、関数適用のとき、 t = t1 t2 とすると、帰納法の仮定からt1は値かステップする。
      + t1 が値であるなら、t2は帰納法の仮定から値かステップできる。
         * t2 が値なら、t1も値なので、[ST_AppAbs]でステップできる。
         * t2 がステップできるなら、t もステップできる。
      + t1 がステップできるなら、t もステップできる。
    - t が、IF式のとき、t = IF t1 THEN t2 ELSE t3 とすると、t1 は値かステップできる。
      + t1 が値なら、それはBool型なので、真ならt2、偽ならt3 にステップできる。
      + t1 がステップできるなら、t もステップできる。
 *)

(* ################################################################# *)
(** ProofCafe ##83 2019/1/19 *)

(** 3. 代入補題 *)
Notation "m '&' { a --> x }" := (update m a x) (at level 20).
(* update Gamma x U |- t を Gamma & {x-->U} と書けるようにする。 *)

(** 代入補題、置換補題 [TAPL 補題9.3.8] *)
(** U型の自由変数xを含む項tの型がTのとき、xにU型の値vを代入しても、[x:=v]tはT型である。 *)
Check substitution_preserves_typing : forall Gamma x U t v T,
    Gamma & {x-->U} |- t \in T -> empty |- v \in U -> Gamma |- [x:=v]t \in T.
(** 補足説明： *)

(** One technical subtlety in the statement of the lemma is that we
    assume v has type U in the empty context — in other words, we
    assume v is closed.

    空な文脈でvは型Uであることを前提とする - 言い換えると、vは閉じてい
    る（自由変数を持たない）ことを前提とする。
    …これは、Stcl の 置換 Substituion の節の techincal note を反映し
    ている。*)

(** TAPL などでは、より一般的に定義されている。 *)
Check forall Gamma x U t v T,
    Gamma & {x-->U} |- t \in T -> Gamma |- v \in U -> Gamma |- [x:=v]t \in T.

(* END *)
