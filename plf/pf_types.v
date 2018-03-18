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
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Import Imp. 
Require Import Smallstep.
Require Import Types.

Hint Constructors multi.

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

(* END *)
