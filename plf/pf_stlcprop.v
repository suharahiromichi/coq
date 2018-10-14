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


(* END *)
