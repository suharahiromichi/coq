(* ProofCafe SF/PLF Support Page *)
(* Smallstep.v *)

(*
これは、ProofCafe の Software Foundations, Vol.2 Programming Language Foundations の
勉強会のサポートページです。復習などに利用しててください。

本ファイルの実行は、本ファイルを pfl ディレクトリの中に混ぜて置くか、
pfl のオリジナルの適当なファイルの適当な場所にcopy&pasteすることで可能です。
 *)

(* ご注意：

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

(* ProofCafe #72 2018/01/20 *)

(** * A Toy Language *)

Module PF_SimpleArith1.
Import SimpleArith1.

(* tm 型のコンストラクタ *)
Check C : nat -> tm.
Check P : tm -> tm -> tm.

(* tm の例 *)
Check (P (P (C 1) (P (C 2) (C 3)))
         (P (C 11) (P (C 12) (C 13)))) : tm. (* tm 型として正しい。 *)

Definition test := (P (P (C 1) (P (C 2) (C 3)))
                      (P (C 11) (P (C 12) (C 13)))).

(* big-step *)
Print evalF.                                (* evalF の定義 *)
Check evalF test : nat.
Compute evalF test.    (* = 42 : nat *)

(* small-step *)

(* 導入された公理 *)
Check ST_PlusConstConst :
  forall n1 n2, (P (C n1) (C n2) ==> C (n1 + n2)).
Check ST_Plus1 :
  forall t1 t1' t2, (t1 ==> t1') -> (P t1 t2 ==> P t1' t2).
Check ST_Plus2 :
  forall (n1 : nat) (t2 t2' : tm),
    t2 ==> t2' -> P (C n1) t2 ==> P (C n1) t2'.

Check test ==> (P (P (C 1) (C 5))
                  (P (C 11) (P (C 12) (C 13)))).

Compute test ==> (P (P (C 1) (C 5))
                  (P (C 11) (P (C 12) (C 13)))).


(*
Small-stepのひとつのステップでやっていること：

「==>」の左辺の、最も左（で最も深いところ）にある 「P (C n1) (C n2)」を探す。
これを 「C (n1 + n2)」 に書き換えたものを「==>」の右辺とする。
*)

Goal test ==> (P (P (C 1) (C 5))
                 (P (C 11) (P (C 12) (C 13)))).
Proof.
  constructor.
  constructor.
  constructor.
  Show Proof.

  Restart.
  apply ST_Plus1.
  apply ST_Plus2.
  apply ST_PlusConstConst.
Qed.

(*
以下はうまくいかない例：
 *)
(*
最も左でなければならない。
 *)
Goal test ==> (P (P (C 1) (P (C 2) (C 3)))
                 (P (C 11) (C 25))).
Proof.
  admit.                                    (* OK. *)
Admitted.

(*
2回分はできない。
 *)
Goal test ==> (P (C 6)
                 (P (C 11) (P (C 12) (C 13)))).
Proof.
  constructor.
  admit.                                    (* OK. *)
Admitted.

End PF_SimpleArith1.

(* END *)
