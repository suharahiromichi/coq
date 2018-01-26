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

(* inversion を使う典型的な証明 *)

Theorem step_deterministic'' : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  
  induction Hy1 as [|t1 t1' t2 H1 IHHy1 |n t1' t2 H1 IHHy1]; intros y2 Hy2.
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
  - inversion Hy2; subst.   (* Hy2 にコンストラクタを逆に適用する。 *)
    (* ST_PlusConstConst の場合、
       Hy2 : P (C n1) (C n2) ==> C (n1 + n2)
       y2 = C (n1 + n2),
       Goal : C (n1 + n2) = C (n1 + n2)
     *)
    + reflexivity.
    (* ST_Plus1 の場合、
       H2 : C n1 ==> t1'
       これはコンストラクトできない（矛盾） *)
    + now inversion H2.                (* 矛盾は inversion で消す！ *)
    (* ST_Plus2 の場合、
       H2 : C n2 ==> t2'
       これはコンストラクトできない（矛盾） *)
    + now inversion H2.                (* 矛盾は inversion で消す！ *)
      
  - inversion Hy2; subst.   (* Hy2 にコンストラクタを逆に適用する。 *)
    (*  ST_PlusConstConst の場合、
        H1 : C n1 ==> t1'
        これはコンストラクトできない（矛盾） *)
    + now inversion H1.                (* 矛盾は inversion で消す！ *)
    (* ST_Plus1 の場合、
       IHHy1 : forall y2 : tm, t1 ==> y2 -> t1' = y2、帰納法
       Goal : P t1' t2 = P t1'0 t2
    *)
    + now rewrite <- (IHHy1 t1'0).      (* generalize dependent y2. *)
    (* ST_Plus2 の場合、
       H1 : C n1 ==> t1'
       これはコンストラクトできない（矛盾） *)
    + now inversion H1.                    (* 矛盾は inversion で消す！ *)

  - inversion Hy2; subst.   (* Hy2 にコンストラクタを逆に適用する。 *)
    (*  ST_PlusConstConst の場合、
       H1 : C n2 ==> t2
       これはコンストラクトできない（矛盾） *)
    + now inversion H1.                    (* 矛盾は inversion で消す！ *)
    (* ST_Plus1 の場合、
       H3 : C n ==> t1'0
       これはコンストラクトできない（矛盾） *)
    + now inversion H3.                    (* 矛盾は inversion で消す！ *)
    (* ST_Plus2 の場合、
       IHHy1 : forall y2 : tm, t1 ==> y2 -> t1' = y2、帰納法
       Goal : P (C n) t2 = P (C n) t2'
     *)
    + now rewrite <- (IHHy1 t2').       (* generalize dependent y2. *)
Qed.          


Theorem step_deterministic' : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2; subst.
    + reflexivity.
    + easy.
    + easy.
  - inversion Hy2; subst.
    + easy.
    + now rewrite <- (IHHy1 t1'0).      (* generalize dependent y2. *)
    + easy.
  - inversion Hy2; subst.
    + easy.
    + easy.
    + now rewrite <- (IHHy1 t2'0).      (* generalize dependent y2. *)
Qed.

Theorem step_deterministic : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try easy.
  - now rewrite <- (IHHy1 t1'0).
  - now rewrite <- (IHHy1 t2'0).
Qed.

End PF_SimpleArith2.

(* ================================================================= *)
(** ** Values *)

(* redo_determinism のヒント：
   value はひとつだけだが、コンストラクタ v_const を持つ。
   それが前提にあるならば、場合分けをする必要がある。
*)

(* ================================================================= *)
(** ** Strong Progress and Normal Forms *)

(* 強進行性 *)
Theorem strong_progress : forall t : tm,
    value t \/ (exists t', t ==> t').
Proof.
  induction t.                      (* q t を証明したい命題とし、tで帰納する。 *)
  - left.                           (* 帰納の底 q (C n) *)
    now apply v_const.
  - right.              (* 帰納の途中 : q t1 -> q t2 -> q (P t1 t2) *)
    destruct IHt1 as [H11 | H12].         (* 選言を場合分けする。 *)
    (* IHt1 の左側 *)
    + destruct IHt2 as [H21 | H22].       (* 選言を場合分けする。 *)
      (* IHt2 の左側 *)
      * destruct H11 as [n1 H11'].        (* value を場合分けする。 *)
        destruct H21 as [n2 H21'].        (* value を場合分けする。 *)
        exists (C (n1 + n2)).
        now apply ST_PlusConstConst.
      (* IHt2 の右側 *)
      * destruct H22 as [t' H22'].       (* exists を場合分けする。 *)
        exists (P t1 t').
        now apply ST_Plus2.
    (* IHt1 の右側 *)
    + destruct H12 as [t' H12'].         (* exists を場合分けする。 *)
      exists (P t' t2).
      now apply ST_Plus1.
Qed.

(* 正規形 *)
Print normal_form.
(*                                        not
fun (X : Type) (R : relation X) (t : X) => ~ (exists t' : X, R t t')
     : forall X : Type, relation X -> X -> Prop
 *)

(* R には step（==>）を渡すなら、
正規形 t は、t ==> t' なる t'が存在しない（もうstepできない）。 *)

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. (* ゴールが Define されたものの場合 *)
  intros v H.         (* ゴールに ∀や->がある場合。ただし、やりすぎに注意 *)
  destruct H.         (* 前提がデータ型のとき、帰納的でないなら場合分けする。 *)
  intro contra.       (* ゴールが否定のとき。引数の無い intros ではだめ。 *)
  destruct contra.    (* 前提が exists のとき *)
  easy.               (* 前提が矛盾（コンストラクトできない）場合 *) (* inversion H. *)
Qed.

Lemma l_strong_progress__nf_is_value : forall t,
    (value t \/ (exists t', t ==> t')) -> normal_form step t -> value t.
Proof.
  unfold normal_form.
  intros t G H.
  destruct G.              (* 前提が \/ のとき、左右で場合分けする。 *)
  (* 左側 *)
  + easy.                   (* 前提がゴールと同じ。 *) (* apply H0. *)
  (* 右側 *)
  + easy.                         (* 矛盾した前提があるとき。 *)
    (* exfalso. apply H. assumption. *) 
Qed.

Lemma nf_is_value : forall t,
    normal_form step t -> value t.
Proof.
  intros t.
  apply l_strong_progress__nf_is_value.
  apply strong_progress.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split.                                    (* ゴールが <-> のとき *)
  - now apply nf_is_value.
  - now apply value_is_nf.
Qed.

(*
なぜこれが興味深いのでしょう？ 2つの理由があります:

なぜならvalue(値)は構文的概念です。つまり項の形を見ることで定義されま
す。一方normal_form(正規形)は意味論的なものです。 つまり項がどのように
ステップを進むかによって定義されます。 この2つの概念が一致することは自
明ではないのです!

実際、正規形と値の概念が一致「しない」言語はたくさん存在します。
*)
             
(* END *)

(*
Home The Coq Proof Assistant Chapter 8  Tactics

8.8.5  easy

This tactic tries to solve the current goal by a number of standard closing steps.
In particular, it tries to close the current goal using the closing tactics trivial, reflexivity, symmetry, contradiction and inversion of hypothesis. (略)

Variant:
now tactic
Run tactic followed by easy. This is a notation for tactic; easy.
 *)

(*
まじかんと さんのページから：

証明事例集: 前提が……のとき
https://magicant.github.io/programmingmemo/coq/byhyp.html

証明事例集: ゴールが……のとき
https://magicant.github.io/programmingmemo/coq/bygoal.html
 *)

