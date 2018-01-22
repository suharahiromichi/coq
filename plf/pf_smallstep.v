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

(* ################################################################# *)
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

(* ProofCafe #73 2018/02/17 予定 *)

(* ################################################################# *)
(** * Relations *)

Module PF_SimpleArith2.
Import PF_SimpleArith1.
Import SimpleArith1.

(* 二項関係 R が決定的である、という命題 *)
Check @deterministic : forall X : Type, relation X -> Prop.

(*
二項関係が決定的 <-> 二項関係は部分関数 partial function である。 
なぜなら、 R x y が決定的ならxに対してyが唯一決まるので関数っぽいけれども、
任意のxに対してyが決まるとは限らないので、部分関数である。

なお、任意のxに対してyが決まる全域関数は、部分関数の一種である。
*)

Theorem step_deterministic : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; try now subst.
  - now rewrite <- (IHHy1 t1'0).      (* generalize dependent y2. *)
  - now rewrite <- (IHHy1 t2'0).      (* generalize dependent y2. *)
Qed.

Theorem step_deterministic' : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2.
    + reflexivity.
    + now subst.
    + now subst.
  - inversion Hy2.
    + now subst.
    + now rewrite <- (IHHy1 t1'0).      (* generalize dependent y2. *)
    + now subst.
  - inversion Hy2.
    + now subst.
    + now subst.
    + now rewrite <- (IHHy1 t2'0).      (* generalize dependent y2. *)
Qed.

Theorem step_deterministic'' : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  
  induction Hy1; intros y2 Hy2.
  (*
  Hy1 : x ==> y1 をコンストラクタで場合分けしたものが、Hy2 である。

  ST_PlusConstConst の場合：
    Hy2 : P (C n1) (C n2) ==> y2
    x = P (C n1 n2) なので、
    ゴールは C (n1 + n2) = y2 である。

  ST_Plus1 の場合：
    Hy2 : P t1 t2 ==> y2
    x = P t1 t2 なので、
    ゴールは P t1' t2 = y2

  ST_Plus2 の場合 :
    Hy2 : P v1 t2 ==> y2
    x = P v1 t2 なので、
    ゴールは P v1 t2' = y2
 *)
  
(*
   Hy2 : P (C n1) (C n2) ==> y2
  ============================
   C (n1 + n2) = y2
*)
  (* Hy2 にコンストラクタを逆に適用する。 *)
  - inversion Hy2; subst.
    (*  ST_PlusConstConst の場合、
       Hy2 : P (C n1) (C n2) ==> C (n1 + n2)
       y2 = C (n1 + n2),
       Goal : C (n1 + n2) = C (n1 + n2)
     *)
    + reflexivity.
    (* ST_Plus1 の場合、
       Hy2 : P (C n1) (C n2) ==> P t1' (C n2)、
       これはコンストラクトできない（矛盾） *)
    + now inversion Hy2.                    (* 矛盾は inversion で消す！ *)
    (* ST_Plus2 の場合、
       Hy2 : P (C n1) (C n2) ==> P (C n1) t2'、
       これはコンストラクトできない（矛盾） *)
    + now inversion Hy2.
      
  (* Hy2 にコンストラクタを逆に適用する。 *)
  - inversion Hy2; subst.
    (*  ST_PlusConstConst の場合、
       Hy2 : P (C n1) (C n2) ==> C (n1 + n2)
       y2 = C (n1 + n2),
       Goal : P t1' (C n2) = C (n1 + n2)
     *)
    + now inversion Hy2.                    (* 矛盾は inversion で消す！ *)
    (* ST_Plus1 の場合、
       Hy2 : P (C n1) (C n2) ==> P t1' (C n2)、
       これはコンストラクトできない（矛盾） *)
    + now rewrite <- (IHHy1 t1'0).      (* generalize dependent y2. *)
    (* ST_Plus2 の場合、
       Hy2 : P (C n1) (C n2) ==> P (C n1) t2'、
       これはコンストラクトできない（矛盾） *)
      Admitted.
 *)

End PF_SimpleArith2.

(* END *)
