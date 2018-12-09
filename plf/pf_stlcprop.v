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
(** ProofCafe ##80 2018/10/20 *)

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

(* **** *)
(* 補題 *)
(* **** *)

(** 正準形、標準型 [TAPL 補題9.3.4] *)
(** 進行性 Progress を証明するための補題である。 *)
(** 項の型がBoolで、項が値なら、その項はtrueかfalse(Bool値)である。 *)
Check canonical_forms_bool :
  forall t : tm, empty |- t \in TBool -> value t -> t = ttrue \/ t = tfalse.
(** 項の型が関数抽象で、項が値なら、その項は適当な項uに対して λx.u である。 *)
Check canonical_forms_fun : forall (t : tm) (T1 T2 : ty),
    empty |- t \in TArrow T1 T2 ->
                      value t -> exists (x : id) (u : tm), t = tabs x T1 u.
(* 証明は、どちらも HVal : value t を destruct で場合分けする。 *)

Notation "m '&' { a --> x }" := (update m a x) (at level 20).
(* update Gamma x U |- t を Gamma & {x-->U} と書けるようにする。 *)



(** 代入補題、置換補題 [TAPL 補題9.3.8] *)
(** U型の自由変数xを含む項tの型がTのとき、xにU型の値vを代入しても、[x:=v]tはT型である。 *)
Check substitution_preserves_typing : forall Gamma x U t v T,
    Gamma & {x-->U} |- t \in T -> empty |- v \in U -> Gamma |- [x:=v]t \in T.
(** 補足説明： *)
(** ふたつめの前提の φ|-v:U は、項vに自由変数が含まれないことを前提とすることを意味する。
    これは、Stcl の 置換 Substituion の節の以下を反映している。
    
（引用）
技術的注釈: 置換は、もし、つまり他の項の変数を置換する項が、 それ自身
に自由変数を含むときを考えると、 定義がよりトリッキーなものになります。
ここで興味があるのは閉じた項についてのstep関係の定義のみなので、そのさ
らなる複雑さは避けることができます。
（引用終）
 *)

(** TAPL などでは、より一般的に定義されている。 *)
Check forall Gamma x U t v T,
    Gamma & {x-->U} |- t \in T -> Gamma |- v \in U -> Gamma |- [x:=v]t \in T.

(* END *)
